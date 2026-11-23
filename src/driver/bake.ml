(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Crane Bake c]: a closed constant computed once, when the command runs,
    and extracted as data.

    The constant is extracted on its own into a temporary unit, its
    initialiser handed to [crane::bake::root] ({!Base.Table.bake_root}); the
    unit is linked with a driver whose [main] is [crane::bake::main] and run.
    The driver writes the value as C++ (theories/cpp/crane_bake.h: a stream
    of words and constant-initialised static blocks), which is recorded with
    the constant ({!Base.Table.record_baked}).  An extraction that declares
    the constant afterwards initialises it from that image and appends the
    image to its implementation file ({!Extract_env.print_structure_to_file}).

    Only a value can be baked: its type is checked to hold no function, type,
    coinductive (lazy, or effectful) value or opaque type, which no image can
    hold.  Every compiler and program run goes through {!Toolchain} and
    {!Subprocess}.

    The bake extracts with the options and mappings in effect at the
    command, and in its own mode (see {!bake_one}), which may differ from
    the user's extraction.  The image is structural (constructor indices,
    then fields in order), so the two need only agree on constructor order
    and on which fields are erased, which they do for one Rocq environment;
    the only representation-dependent part, a static block's element type,
    is checked when the image is read. *)

open Names

let refuse r msg =
  CErrors.user_err Pp.(str "Crane Bake: " ++ Printer.pr_global r ++ spc () ++ str msg ++ str ".")

let rec has_bound_path = function
  | ModPath.MPbound _ -> true
  | ModPath.MPdot (mp, _) -> has_bound_path mp
  | ModPath.MPfile _ -> false

(** Checks that a value of [ty] can be written as data: [what] says, for the
    diagnostic, where in [r]'s type [ty] was found. *)
let check_type env sigma r ty =
  let is_proof env t =
    let s = Retyping.get_sort_of env sigma t in
    EConstr.ESorts.is_prop sigma s || EConstr.ESorts.is_sprop sigma s
  in
  let seen = ref Indset_env.empty in
  let rec value env ~what ty =
    let ty = Reductionops.whd_all env sigma ty in
    match EConstr.kind sigma ty with
    | Sort _ -> refuse r (what ^ " a type, which is not data")
    | Prod _ -> refuse r (what ^ " a function, which is not data")
    | Ind _ | App _ -> (
      let head, args = EConstr.decompose_app sigma ty in
      match EConstr.kind sigma head with
      | Ind (ind, u) -> inductive env ~what ind u args
      | Const (c, _) -> constant ~what c
      | _ -> refuse r (what ^ " a value of a type it cannot see the definition of") )
    | Const (c, _) -> constant ~what c
    | _ -> refuse r (what ^ " a value of a type it cannot see the definition of")
  and constant ~what c =
    (* What [whd_all] leaves a constant: a primitive type, or an axiom --
       data only where a mapping (typed or legacy) says what it is in C++,
       which the bake driver then checks it can write. *)
    if Environ.is_primitive_type env c || Base.Table.is_custom (GlobRef.ConstRef c) then ()
    else
      refuse r (what ^ " a value of the opaque type " ^ Constant.to_string c ^ ", which has no definition to bake")
  and inductive env ~what ind u args =
    let mib, _ = Inductive.lookup_mind_specif env ind in
    if mib.Declarations.mind_finite = Declarations.CoFinite then
      refuse r (what ^ " a coinductive value, which is computed lazily (or an effect)");
    if not (Indset_env.mem ind !seen) then begin
      seen := Indset_env.add ind !seen;
      let params = Array.to_list (Array.sub args 0 (min (Array.length args) mib.Declarations.mind_nparams)) in
      let ncons = Array.length (snd (Inductive.lookup_mind_specif env ind)).Declarations.mind_consnames in
      for j = 1 to ncons do
        let cty = Inductiveops.e_type_of_constructor env sigma ((ind, j), u) in
        let cty = Reductionops.hnf_prod_applist env sigma cty params in
        let rec fields env cty =
          match EConstr.kind sigma (Reductionops.whd_all env sigma cty) with
          | Prod (na, a, b) ->
            if not (is_proof env a) then value env ~what:"holds, in a constructor field," a;
            fields (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, a)) env) b
          | _ -> ()
        in
        fields env cty
      done
    end
  in
  if is_proof env ty then refuse r "is a proof, which extraction erases";
  value env ~what:"is" ty

(** The functor application ([Module FN := F N]) that [mp] or a module
    enclosing it is, or aliases ([Module M := FN]).  Its constants
    are extracted as members of the functor's template ([using FN = F<N>;]),
    which an image cannot initialise for one instantiation. *)
let rec applied_module env mp =
  match mp with
  | ModPath.MPdot (parent, _) -> (
    let applied =
      match Mod_declarations.mod_expr (Environ.lookup_module mp env) with
      | Algebraic (MENoFunctor me) -> application env mp me
      | _ -> None
    in
    match applied with Some _ -> applied | None -> applied_module env parent )
  | ModPath.MPfile _ | ModPath.MPbound _ -> None

(* The functor application [mp], defined by [me], is or aliases. *)
and application env mp : _ Declarations.module_alg_expr -> _ = function
  | MEapply _ -> Some mp
  | MEident target -> applied_module env target
  | MEwith (me, _) -> application env mp me

let check r =
  match r with
  | GlobRef.ConstRef c ->
    if has_bound_path (Constant.modpath c) then
      refuse r "is declared inside a functor or a module type, so it is not closed";
    ( match applied_module (Global.env ()) (Constant.modpath c) with
    | Some mp ->
      refuse r
        ( "is declared in " ^ ModPath.to_string mp
        ^ ", a functor application, so it is a member of the functor's C++ template, not a declaration of \
           its own" )
    | None -> () );
    let env = Global.env () in
    let cb = Environ.lookup_constant c env in
    ( match cb.Declarations.const_body with
    | Declarations.Def _ -> ()
    | _ -> refuse r "has no transparent body to evaluate" );
    if not (Base.Table.is_custom r) then ()
    else refuse r "has a custom extraction, which is what it is extracted as";
    (* Which heads a typed mapping maps: an extraction discovers them when
       it starts, and the check runs before any. *)
    Base.Mapping_discovery.discover ();
    let sigma = Evd.from_env env in
    check_type env sigma r (EConstr.of_constr cb.Declarations.const_type)
  | _ -> refuse r "is not a constant"

(** The C++ name of [r]'s image: unique to the constant, whatever unit
    declares it. *)
let symbol_of = function
  | GlobRef.ConstRef c ->
    let label = Label.to_string (Constant.label c) in
    let safe = String.map (fun ch -> match ch with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> ch | _ -> '_') label in
    let digest = Digest.to_hex (Digest.string (KerName.to_string (Constant.canonical c))) in
    "crane_baked_" ^ safe ^ "_" ^ String.sub digest 0 12
  | _ -> assert false

let rec remove_tree path =
  if Sys.file_exists path then
    if Sys.is_directory path then begin
      Array.iter (fun f -> remove_tree (Filename.concat path f)) (Sys.readdir path);
      try Sys.rmdir path with Sys_error _ -> ()
    end
    else Sys.remove path

(* The files under [dir] with suffix [ext], and the directories holding
   them. *)
let rec files_under dir ext =
  Array.fold_left
    (fun acc f ->
      let path = Filename.concat dir f in
      if Sys.is_directory path then files_under path ext @ acc
      else if Filename.check_suffix f ext then path :: acc
      else acc )
    [] (Sys.readdir dir)

let driver_source header =
  "#include \"crane_bake.h\"\n#include \"" ^ header ^ "\"\n"
  ^ "int main(int argc, char **argv) { return crane::bake::main(argc, argv); }\n"

let fail_with dir msg = CErrors.user_err Pp.(str "Crane Bake: " ++ msg ++ fnl () ++ str ("(files kept in " ^ dir ^ ")"))

(* A compiler's diagnostics, cut to its errors and what follows each: a
   linker's ([Undefined symbols ...]) as well as the compiler's. *)
let errors_of diagnostics =
  let lines = String.split_on_char '\n' diagnostics in
  let rec keep n = function
    | [] -> []
    | l :: rest when n > 0 -> l :: keep (n - 1) rest
    | l :: rest ->
      let is_error =
        let n = String.length l in
        let rec at i = i + 6 <= n && (String.sub l i 6 = "error:" || at (i + 1)) in
        at 0 || String.starts_with ~prefix:"Undefined symbols" l
      in
      if is_error then l :: keep 3 rest else keep 0 rest
  in
  let kept = keep 0 lines in
  String.concat "\n" (List.filteri (fun i _ -> i < 40) (if kept = [] then lines else kept))

(** Bakes [r]: extracts it, compiles and runs the driver, and records the
    image it writes. *)
let bake_one ~opaque_access qualid =
  let r = Smartlocate.global_with_alias qualid in
  check r;
  (* A census that writes no files has no unit to compile: the constant is
     left to be computed at startup. *)
  if Base.Probe.census_dry () then () else
  let symbol = symbol_of r in
  let dir = Filename.temp_dir "crane_bake" "" in
  (* A constant at a library's top level is extracted one file per library,
     as [Crane Separate Extraction] does: the mode a large program is known
     to compile in, where its declaration is a variable initialised at
     startup.  One inside a module is extracted into one file, where its
     declaration is a static member initialised at startup; one file per
     library would make it an accessor, which nothing calls.  Everything
     either records -- the units it claims libraries for, the output
     directory -- is forgotten: the bake is not an extraction of the
     user's. *)
  let modpath = match r with GlobRef.ConstRef c -> Constant.modpath c | _ -> assert false in
  let top_level = match modpath with ModPath.MPfile _ -> true | _ -> false in
  let unit_name = "crane_bake_unit" in
  Vernacstate.System.protect
    (fun () ->
      Goptions.set_string_option_value ~stage:Summary.Stage.Interp
        ["Crane"; "Extraction"; "Output"; "Directory"] dir;
      Base.Table.bake_root := Some r;
      Fun.protect ~finally:(fun () -> Base.Table.bake_root := None) @@ fun () ->
      if top_level then Extract_env.separate_extraction ~opaque_access [qualid]
      else
        Extract_env.full_extraction ~validate:false ~opaque_access
          (Some (Filename.concat dir (unit_name ^ ".cpp"))) [qualid] )
    ();
  let header =
    if top_level then Base.Table.file_of_modfile (MPfile (ModPath.dp modpath)) ^ ".h" else unit_name ^ ".h"
  in
  let sources = files_under dir ".cpp" in
  let include_dirs = List.sort_uniq String.compare (List.map Filename.dirname (files_under dir ".h")) in
  let driver = Filename.concat dir "crane_bake_main.cpp" in
  let oc = open_out_bin driver in
  output_string oc (driver_source header);
  close_out oc;
  let exe = Filename.concat dir "crane_bake_main" in
  (* [Set Crane Bake Flags], then [CRANE_BAKE_FLAGS]: where a build keeps
     the headers a mapping includes. *)
  let flags = Base.Table.bake_flags () ^ " " ^ Option.default "" (Sys.getenv_opt "CRANE_BAKE_FLAGS") in
  let user_flags =
    try Subprocess.split_arguments flags
    with Subprocess.Invalid_arguments m -> fail_with dir Pp.(str ("invalid Crane Bake Flags: " ^ m))
  in
  let runtime = Bake_inputs.runtime_dirs () in
  (* Each source is compiled on its own, so the compiler writes each one's
     dependency file ([-MD], next to its object): the headers the image was
     computed from, which are recorded with it ({!Bake_inputs}). *)
  let flags = ["-O1"; "-w"; "-include"; "crane_bake.h"; "-MD"] @ user_flags in
  let includes = include_dirs @ runtime in
  let compile ?shouldlink ?(extra = []) ?outfile source =
    try Toolchain.compile_cpp ?shouldlink ~includes ~flags:(flags @ extra) ?outfile source with
    | Toolchain.NoClangFound -> fail_with dir Pp.(str "clang++ is not available.")
    | Toolchain.ClangError (_, errors) ->
      fail_with dir Pp.(str "the bake driver failed to compile:" ++ fnl () ++ str (errors_of errors))
  in
  List.iter (fun source -> compile source) sources;
  let objects = List.map (fun source -> Filename.chop_suffix source ".cpp" ^ ".o") sources in
  compile ~shouldlink:true ~extra:objects ~outfile:exe driver;
  let depfiles = List.map (fun source -> Filename.chop_suffix source ".cpp" ^ ".d") sources @ [exe ^ ".d"] in
  let inputs = Bake_inputs.record ~generated:dir (List.filter Sys.file_exists depfiles) in
  let out = Filename.concat dir "image.inc" in
  let result = Subprocess.capture exe [out; symbol; symbol ^ "_"] in
  ( match result.status with
  | Unix.WEXITED 0 -> ()
  | status ->
    fail_with dir
      Pp.(str ("the bake driver failed (exit code " ^ string_of_int (Subprocess.exit_code status) ^ "):")
          ++ fnl () ++ str result.stderr) );
  let image = In_channel.with_open_bin out In_channel.input_all in
  remove_tree dir;
  Base.Table.record_baked r
    {Base.Table.symbol; image; inputs; compiler = Bake_inputs.compiler (); env_flags = Bake_inputs.env_flags ()}

let bake ~opaque_access l = List.iter (bake_one ~opaque_access) l
