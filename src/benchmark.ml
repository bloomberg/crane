(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Implementation of the [Crane Benchmark] command.

    The command validates Rocq subjects, materializes managed or legacy source
    artifacts, compiles the subject/configuration matrix, checks observational
    equivalence, and finally delegates timing to Hyperfine. Temporary artifacts
    are scoped to a single command invocation. *)

open Names
open Libnames

(** Native extraction and compilation backend. *)
type backend =
  | OCaml  (** Rocq's OCaml extraction and [ocamlopt]. *)
  | Cpp  (** Crane's C++ extraction and [clang++]. *)

(** User-facing benchmark subject parsed from the vernacular command. *)
type subject = {
  term : qualid;  (** Rocq definition expected to have type [unit -> string]. *)
  label : string option;  (** Optional display label supplied with [As]. *)
}

(** User-facing compiler configuration parsed after [On]. *)
type configuration = {
  backend : backend;  (** Backend used for extraction and compilation. *)
  source : string option;
      (** Pre-extracted legacy source, or [None] for managed extraction. *)
  flags : string;  (** Compiler arguments in shell-like textual form. *)
}

(** A subject after name resolution, type validation, and label assignment. *)
type validated_subject = {
  benchmark_term : qualid;  (** Original name used to request extraction. *)
  benchmark_ref : GlobRef.t;  (** Resolved transparent constant reference. *)
  benchmark_label : string;  (** Non-empty, unique display label. *)
}

(** Source artifact and backend expressions needed to construct its driver. *)
type artifact = {
  artifact_source : string;  (** Extracted or user-supplied source path. *)
  artifact_callable : string;  (** Qualified benchmark function expression. *)
  artifact_unit : string;  (** Backend expression representing Rocq [tt]. *)
}

(** One successfully compiled cell in the benchmark matrix. *)
type compiled_benchmark = {
  compiled_index : int;  (** Stable, one-based matrix position. *)
  compiled_description : string;  (** Human-readable subject/configuration. *)
  compiled_executable : string;  (** Temporary native executable path. *)
}

(** Source acquisition strategy shared by all configurations in one command. *)
type mode =
  | Managed  (** Crane creates source artifacts from each subject. *)
  | Legacy  (** Every configuration names an existing source with [From]. *)

(** Return the user-facing name of a backend. *)
let backend_name = function OCaml -> "OCaml" | Cpp -> "C++"

(** Report a benchmark failure as a Rocq user error. *)
let benchmark_error message = CErrors.user_err Pp.(str message)

(** Resolve and validate one subject.

    The definition must be a transparent constant convertible to
    [unit -> PrimString.string]. The result retains the global reference needed
    to recover backend-specific generated names. *)
let validate_subject {term; label = requested_label} =
  let open Constr in
  let open Declarations in
  let open Reductionops in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let reference = Smartlocate.global_with_alias term in
  let actual_ty =
    match reference with
    | GlobRef.ConstRef constant ->
      let body = Global.lookup_constant constant in
      ( match body.const_body with
      | Def _ -> EConstr.of_constr body.const_type
      | _ ->
        CErrors.user_err
          Pp.(
            str "Benchmark subject '"
            ++ pr_qualid term
            ++ str "' must be a transparent definition." ) )
    | _ ->
      CErrors.user_err
        Pp.(
          str "Benchmark subject '"
          ++ pr_qualid term
          ++ str "' must be a constant definition." )
  in
  let locate_type path =
    match Nametab.locate (qualid_of_string path) with
    | GlobRef.ConstRef constant ->
      Constr.mkConstU (constant, UVars.Instance.empty)
    | GlobRef.IndRef (inductive, _) ->
      Constr.mkIndU ((inductive, 0), UVars.Instance.empty)
    | GlobRef.ConstructRef ((inductive, index), _) ->
      Constr.mkConstructU (((inductive, 0), index), UVars.Instance.empty)
    | _ ->
      CErrors.user_err
        Pp.(str "Could not locate a type required by Crane Benchmark.")
  in
  let unit_ty = locate_type "Corelib.Init.Datatypes.unit" in
  let string_ty = locate_type "Corelib.Strings.PrimString.string" in
  let expected_ty = Term.mkArrow unit_ty Sorts.Relevant string_ty in
  let () =
    if
      not
        (is_conv env sigma actual_ty (EConstr.of_constr expected_ty))
    then
      let actual_ty_pp = Printer.pr_econstr_env env sigma actual_ty in
      let expected_ty_pp = Printer.pr_constr_env env sigma expected_ty in
      CErrors.user_err
        Pp.(
          str "Benchmark subject '"
          ++ pr_qualid term
          ++ str "' has the wrong type:"
          ++ fnl ()
          ++ str "Actual type: "
          ++ actual_ty_pp
          ++ fnl ()
          ++ str "Expected type: "
          ++ expected_ty_pp )
  in
  let benchmark_label =
    match requested_label with
    | Some label when String.equal label "" ->
      benchmark_error "Crane Benchmark labels cannot be empty."
    | Some label -> label
    | None -> string_of_qualid term
  in
  {benchmark_term = term; benchmark_ref = reference; benchmark_label}

(** Ensure every validated subject has a distinct display label. *)
let validate_unique_labels subjects =
  let rec loop seen = function
    | [] -> ()
    | subject :: rest ->
      if List.mem subject.benchmark_label seen then
        benchmark_error
          ( "Duplicate Crane Benchmark label: \""
          ^ subject.benchmark_label
          ^ "\"." )
      else
        loop (subject.benchmark_label :: seen) rest
  in
  loop [] subjects

(** Validate a matrix's source mode and classify it as managed or legacy.

    Managed and legacy configurations cannot be mixed. Legacy mode accepts only
    a single subject because all configurations refer to pre-extracted code. *)
let validate_mode subjects configurations =
  let managed =
    List.for_all
      (fun configuration -> Option.is_empty configuration.source)
      configurations
  in
  let has_managed =
    List.exists
      (fun configuration -> Option.is_empty configuration.source)
      configurations
  in
  if (not managed) && has_managed then
    benchmark_error
      "Crane Benchmark cannot mix managed entries with legacy 'From' entries.";
  if (not managed) && not (Int.equal (List.length subjects) 1) then
    benchmark_error
      "Legacy 'From' entries support exactly one benchmark subject. Remove \
       'From' to benchmark multiple definitions with managed extraction.";
  if managed then Managed else Legacy

(** Return the exact C++ expression for Rocq's [tt] constructor under the
    currently active extraction mappings and renaming state. *)
let cpp_unit () =
  match Table.resolve_tt_ctor () with
  | Some tt when Table.is_custom tt -> Table.find_custom tt
  | Some (GlobRef.ConstructRef ((kn, index), constructor_index)) ->
    let unit_ref = GlobRef.IndRef (kn, index) in
    Common.pp_global Common.Type unit_ref
    ^ "::"
    ^ Table.enum_ctor_name_of_ref kn index constructor_index
  | _ ->
    CErrors.anomaly
      Pp.(str "Crane Benchmark could not resolve Rocq's unit constructor.")

(** Return the exact qualified C++ callable and unit expression for [reference].

    This function must run before Crane resets the extraction naming tables. *)
let cpp_entrypoint reference =
  let base, _ = Table.labels_of_ref reference in
  Common.push_visible base [];
  Fun.protect
    ~finally:Common.pop_visible
    (fun () -> (Common.pp_global Common.Term reference, cpp_unit ()))

(** Split a non-empty global label path into its module prefix and final label. *)
let split_last_label labels =
  let rec split acc = function
    | [] -> CErrors.anomaly Pp.(str "Empty global reference name.")
    | [last] -> (List.rev acc, last)
    | label :: rest -> split (label :: acc) rest
  in
  split [] labels

(** Construct the best-effort qualified C++ name used by a legacy source file.

    Legacy mode has no live extraction naming state, so the name is derived from
    the reference's raw labels and Crane's reserved-identifier escaping. *)
let raw_qualified_name reference =
  let _, labels = Table.labels_of_ref reference in
  let modules, term = split_last_label labels in
  let modules =
    List.map
      (fun label ->
        Table.escape_reserved_struct_name (Common.module_label_name label) )
      modules
  in
  String.concat "::" (modules @ [Common.module_label_name term])

(** Construct the qualified name emitted by Rocq's built-in OCaml extraction. *)
let ocaml_callable reference =
  let _, labels = Table.labels_of_ref reference in
  let modules, _ = split_last_label labels in
  let term =
    Extraction_plugin.Common.pp_global_name
      Extraction_plugin.Common.Term
      reference
  in
  String.concat "." (List.map Label.to_string modules @ [term])

(** Convert an extracted primitive-string expression to [Stdlib.string] when
    Rocq's default [Pstring.t] representation is active. *)
let ocaml_output expression =
  let string_ref =
    Nametab.locate (qualid_of_string "Corelib.Strings.PrimString.string")
  in
  if Extraction_plugin.Table.is_custom string_ref then
    expression
  else
    "Pstring.to_string (" ^ expression ^ ")"

(** Construct the conventional C++ [tt] expression used by legacy artifacts. *)
let legacy_cpp_unit () =
  match Table.resolve_tt_ctor () with
  | Some tt when Table.is_custom tt -> Table.find_custom tt
  | Some (GlobRef.ConstructRef ((kn, index), constructor_index)) ->
    let unit_name =
      String.capitalize_ascii
        (Id.to_string
           (Table.safe_basename_of_global (GlobRef.IndRef (kn, index))) )
    in
    unit_name ^ "::" ^ Table.enum_ctor_name_of_ref kn index constructor_index
  | _ ->
    CErrors.anomaly
      Pp.(str "Crane Benchmark could not resolve Rocq's unit constructor.")

(** Read all bytes from a source file and close the channel reliably. *)
let read_file filename =
  let ic = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(** Replace a file with [contents], closing the channel reliably. *)
let write_file filename contents =
  let oc = open_out_bin filename in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () -> output_string oc contents)

(** Copy [source] to [destination] and append generated driver code [suffix]. *)
let copy_with_suffix source destination suffix =
  write_file destination (read_file source ^ suffix)

(** Recursively remove a benchmark-owned temporary directory tree. *)
let rec remove_directory_tree path =
  if Sys.file_exists path then
    if Sys.is_directory path then (
      Array.iter
        (fun entry -> remove_directory_tree (Filename.concat path entry))
        (Sys.readdir path);
      Unix.rmdir path )
    else
      Sys.remove path

(** Return the distinct backends requested by [configurations], preserving their
    first-occurrence order. Managed extraction needs one artifact per backend,
    not one artifact per compiler-flag variant. *)
let unique_backends configurations =
  List.fold_left
    (fun backends configuration ->
      if List.mem configuration.backend backends then
        backends
      else
        backends @ [configuration.backend] )
    []
    configurations

(** Build a deterministic temporary source stem for a subject/backend pair. *)
let artifact_stem subject_index = function
  | Cpp -> "subject_" ^ string_of_int (subject_index + 1) ^ "_cpp"
  | OCaml -> "subject_" ^ string_of_int (subject_index + 1) ^ "_ocaml"

(** Extract one managed source artifact and determine its callable expression.

    C++ callable metadata is captured while Crane's exact renaming state remains
    live. OCaml callable names are derived using the built-in extraction naming
    rules. *)
let extract_managed_artifact
    ~opaque_access
    ~temp_dir
    subject_index
    subject
    backend =
  let stem = artifact_stem subject_index backend in
  match backend with
  | Cpp ->
    let source = Filename.concat temp_dir (stem ^ ".cpp") in
    let callable, unit =
      Extract_env.full_extraction_with_result
        ~opaque_access
        (Some source)
        [subject.benchmark_term]
        (fun () -> cpp_entrypoint subject.benchmark_ref)
    in
    {
      artifact_source = source;
      artifact_callable = callable;
      artifact_unit = unit;
    }
  | OCaml ->
    let source = Filename.concat temp_dir (stem ^ ".ml") in
    Extraction_plugin.Extract_env.full_extraction
      ~opaque_access
      (Some source)
      [subject.benchmark_term];
    {
      artifact_source = source;
      artifact_callable = ocaml_callable subject.benchmark_ref;
      artifact_unit = "()";
    }

(** Materialize every unique subject/backend artifact required by a managed
    matrix. Results are keyed by zero-based subject index and backend. *)
let materialize_managed ~opaque_access ~temp_dir subjects configurations =
  let backends = unique_backends configurations in
  List.mapi
    (fun subject_index subject ->
      List.map
        (fun backend ->
          ( (subject_index, backend),
            extract_managed_artifact
              ~opaque_access
              ~temp_dir
              subject_index
              subject
              backend ) )
        backends )
    subjects
  |> List.flatten

(** Resolve a legacy source relative to Crane's output directory and verify that
    it exists. *)
let resolve_legacy_source source =
  let source =
    if Filename.is_relative source then
      Filename.concat (Table.output_directory ()) source
    else
      source
  in
  if not (Sys.file_exists source) then
    benchmark_error ("Benchmark source file not found: " ^ source);
  source

(** Describe a pre-extracted source and the call expression needed by its
    backend-specific driver. *)
let legacy_artifact subject configuration =
  let source =
    match configuration.source with
    | Some source -> resolve_legacy_source source
    | None -> assert false
  in
  match configuration.backend with
  | Cpp ->
    {
      artifact_source = source;
      artifact_callable = raw_qualified_name subject.benchmark_ref;
      artifact_unit = legacy_cpp_unit ();
    }
  | OCaml ->
    {
      artifact_source = source;
      artifact_callable = ocaml_callable subject.benchmark_ref;
      artifact_unit = "()";
    }

(** Build the display name used in compiler errors and Hyperfine output. *)
let description subject configuration =
  subject.benchmark_label
  ^ " ["
  ^ backend_name configuration.backend
  ^ if String.equal configuration.flags "" then
      "]"
    else
      ", " ^ configuration.flags ^ "]"

(** Generate the backend-specific program appended to an artifact.

    Each driver invokes the benchmark with [tt] and prints the returned string,
    providing both the value checked for equivalence and the timed workload. *)
let driver_suffix artifact = function
  | Cpp ->
    "\n#include <iostream>\nint main() {\n  std::cout << ("
    ^ artifact.artifact_callable
    ^ "("
    ^ artifact.artifact_unit
    ^ ")) << std::endl;\n  return 0;\n}\n"
  | OCaml ->
    let call = artifact.artifact_callable ^ " " ^ artifact.artifact_unit in
    "\nlet () = Stdlib.print_endline (" ^ ocaml_output call ^ ")\n"

(** Parse a compiler-flags string and translate parser failures into Rocq user
    errors with benchmark-specific wording. *)
let parse_flags flags =
  try Subprocess.split_arguments flags
  with Subprocess.Invalid_arguments message ->
    benchmark_error ("Invalid compiler flags: " ^ message ^ ".")

(** Create and compile one matrix cell.

    The source artifact is copied into a temporary driver, the requested flags
    are parsed into argv elements, and backend-specific compiler failures are
    reported with the cell's stable index and description. *)
let compile_artifact
    ~temp_dir
    ~index
    subject
    configuration
    artifact =
  let extension = match configuration.backend with Cpp -> ".cpp" | OCaml -> ".ml" in
  let driver =
    Filename.concat temp_dir ("driver_" ^ string_of_int index ^ extension)
  in
  copy_with_suffix
    artifact.artifact_source
    driver
    (driver_suffix artifact configuration.backend);
  let executable =
    Filename.concat temp_dir ("benchmark_" ^ string_of_int index)
  in
  let compiler_flags = parse_flags configuration.flags in
  let description = description subject configuration in
  ( match configuration.backend with
  | Cpp ->
    ( try
        Toolchain.compile_cpp
          ~shouldlink:true
          ~includes:[Filename.dirname artifact.artifact_source]
          ~flags:compiler_flags
          ~outfile:executable
          driver
      with
    | Toolchain.NoClangFound ->
      benchmark_error "clang++ is not available: cannot run C++ benchmark."
    | Toolchain.ClangError (_, errors) ->
      benchmark_error
        ( "Failed to compile benchmark "
        ^ string_of_int index
        ^ " ("
        ^ description
        ^ "):\n"
        ^ errors ) )
  | OCaml ->
    ( try
        Toolchain.compile_ocaml
          ~shouldlink:true
          ~includes:[Filename.dirname artifact.artifact_source]
          ~flags:compiler_flags
          ~outfile:executable
          driver
      with
    | Toolchain.NoOcamloptFound ->
      benchmark_error "ocamlopt is not available: cannot run OCaml benchmark."
    | Toolchain.OcamloptError (_, errors) ->
      benchmark_error
        ( "Failed to compile benchmark "
        ^ string_of_int index
        ^ " ("
        ^ description
        ^ "):\n"
        ^ errors ) ) );
  {
    compiled_index = index;
    compiled_description = description;
    compiled_executable = executable;
  }

(** Compile the Cartesian product of [subjects] and [configurations] in
    subject-major order. Managed artifacts are looked up by subject/backend;
    legacy artifacts are described directly from each configuration. *)
let compile_matrix ~temp_dir ~mode ~artifacts subjects configurations =
  let configuration_count = List.length configurations in
  List.mapi
    (fun subject_index subject ->
      List.mapi
        (fun configuration_index configuration ->
          let index =
            (subject_index * configuration_count) + configuration_index + 1
          in
          let artifact =
            match mode with
            | Managed -> List.assoc (subject_index, configuration.backend) artifacts
            | Legacy -> legacy_artifact subject configuration
          in
          compile_artifact
            ~temp_dir
            ~index
            subject
            configuration
            artifact )
        configurations )
    subjects
  |> List.flatten

(** Limit an observed program output to a readable diagnostic excerpt. *)
let output_excerpt output =
  let limit = 500 in
  if String.length output <= limit then
    output
  else
    String.sub output 0 limit ^ "..."

(** Execute one compiled benchmark once and return its stdout.

    This preflight execution is intentionally separate from Hyperfine so failed
    programs and unequal results never produce misleading timing comparisons. *)
let execute benchmark =
  let output = Subprocess.capture benchmark.compiled_executable [] in
  ( match output.status with
  | Unix.WEXITED 0 -> ()
  | status ->
    benchmark_error
      ( "Benchmark "
      ^ string_of_int benchmark.compiled_index
      ^ " ("
      ^ benchmark.compiled_description
      ^ ") exited with status "
      ^ string_of_int (Subprocess.exit_code status)
      ^ ":\n"
      ^ output.stderr ) );
  (benchmark, output.stdout)

(** Run every matrix cell and require byte-for-byte identical stdout, using the
    first cell as the observational baseline. *)
let verify_outputs benchmarks =
  match List.map execute benchmarks with
  | [] -> CErrors.anomaly Pp.(str "Crane Benchmark received an empty matrix.")
  | (baseline, expected) :: candidates ->
    List.iter
      (fun (candidate, actual) ->
        if not (String.equal expected actual) then
          benchmark_error
            ( "Benchmark outputs differ; Hyperfine was not run.\n"
            ^ "Expected from "
            ^ baseline.compiled_description
            ^ ":\n"
            ^ output_excerpt expected
            ^ "\nActual from "
            ^ candidate.compiled_description
            ^ ":\n"
            ^ output_excerpt actual ) )
      candidates

(** Replace temporary executable paths in Hyperfine output with stable indices
    and human-readable descriptions. Repeated occurrences use only the index. *)
let replace_paths_with_names benchmarks output =
  List.fold_right
    (fun benchmark output ->
      let name = "Benchmark " ^ string_of_int benchmark.compiled_index in
      let first = ref true in
      Str.global_substitute
        (Str.regexp (Str.quote benchmark.compiled_executable))
        (fun _ ->
          if !first then (
            first := false;
            name ^ " (" ^ benchmark.compiled_description ^ ")" )
          else
            name )
        output )
    benchmarks
    output

(** Remove Hyperfine's own [Benchmark N:] prefix because Crane supplies stable
    matrix indices in the replacement descriptions. *)
let clean_benchmark_lines output =
  let benchmark_prefix = Str.regexp "^\\(Benchmark [0-9]+: \\)" in
  Str.global_substitute benchmark_prefix (fun _ -> "") output

(** Invoke Hyperfine for all verified executables and report its rewritten
    output through Rocq's feedback channel. *)
let run_hyperfine benchmarks =
  let output =
    Subprocess.capture
      "hyperfine"
      ( "--style=basic"
      :: List.map
           (fun benchmark -> benchmark.compiled_executable)
           benchmarks )
  in
  match output.status with
  | Unix.WEXITED 0 ->
    output.stdout
    |> clean_benchmark_lines
    |> replace_paths_with_names benchmarks
    |> Pp.str
    |> Feedback.msg_info
  | status ->
    benchmark_error
      ( "Hyperfine failed with status "
      ^ string_of_int (Subprocess.exit_code status)
      ^ ":\n"
      ^ output.stderr )

(** Validate, materialize, compile, preflight, and time a benchmark matrix.

    A fresh temporary directory owns every generated source, driver, compiler
    artifact, and executable; it is recursively removed on success or failure. *)
let run ~opaque_access requested_subjects configurations =
  if not (Subprocess.executable_available "hyperfine") then
    benchmark_error "Hyperfine is not available: cannot run benchmarks.";
  let subjects = List.map validate_subject requested_subjects in
  validate_unique_labels subjects;
  let mode = validate_mode subjects configurations in
  let temp_dir = CUnix.mktemp_dir "crane_benchmark" "" in
  Fun.protect
    ~finally:(fun () -> remove_directory_tree temp_dir)
    (fun () ->
      let artifacts =
        match mode with
        | Managed ->
          materialize_managed
            ~opaque_access
            ~temp_dir
            subjects
            configurations
        | Legacy -> []
      in
      let benchmarks =
        compile_matrix
          ~temp_dir
          ~mode
          ~artifacts
          subjects
          configurations
      in
      verify_outputs benchmarks;
      run_hyperfine benchmarks )
