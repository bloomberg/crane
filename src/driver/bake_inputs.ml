(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a baked image was computed from outside the Rocq document, and
    whether it still holds.

    A [Crane Bake] runs C++ (theories/cpp/crane_bake.h, and every header the
    extracted unit includes) compiled by [clang++] with [CRANE_BAKE_FLAGS], and
    the image it writes is kept in the library ({!Base.Table.record_baked}).
    None of those inputs is a dependency a build system sees of the [.vo]: a
    changed runtime header, compiler or flag leaves the image as the old code
    wrote it, which the new code may read differently.  So the bake records
    them ({!record}: the files the compiler's dependency output lists, with
    their digests), and an extraction that uses the image checks them first
    ({!check}), refusing a stale image rather than emitting it.

    The check does not re-bake: a bake is a nested extraction, which cannot
    run inside the one in progress.  [Set Crane Bake Flags] is not compared,
    since it is in the document, which the build system does see; libraries
    linked into the driver (BDE's) are not recorded.  The other half is a
    dune dependency: theories/RuntimeHeaders.v
    (scripts/runtime-headers-digest.sh) names a definition after the runtime
    headers' digest and [Crane.Extraction] requires it, so editing a header
    rebuilds every file that loads Crane before this check would refuse its
    image. *)

open Names

(* Crane's runtime headers: [theories/cpp] of the tree the loaded Crane
   theory was built in, whichever build directory ([_build/default],
   [_build/census/default], ...) that was. *)
let runtime_include () =
  let has_runtime dir = Sys.file_exists (Filename.concat dir "crane_bake.h") in
  match Toolchain.crane_runtime_include () with
  | Some dir when has_runtime dir -> Some dir
  | found -> (
    let marker = Filename.dir_sep ^ "_build" ^ Filename.dir_sep in
    let source_tree dir =
      let n = String.length marker in
      let rec find i =
        if i + n > String.length dir then None
        else if String.sub dir i n = marker then Some (String.sub dir 0 i)
        else find (i + 1)
      in
      find 0
    in
    match Option.bind found source_tree with
    | Some root ->
      let dir = Filename.concat (Filename.concat root "theories") "cpp" in
      if has_runtime dir then Some dir else found
    | None -> found )

(** The include directories of Crane's runtime, in search order: a BDE build
    reads the BDE flavour of a header first (scripts/compile-bde.sh). *)
let runtime_dirs () =
  match runtime_include () with
  | Some d when Toolchain.is_bde () ->
    let bde = Filename.concat (Filename.dirname d) "cpp_bde" in
    if Sys.file_exists bde then [bde; d] else [d]
  | Some d -> [d]
  | None -> []

(* The directory holding the runtime's include directories ([theories]):
   runtime headers are named relative to it, so a library baked against one
   checkout or installation of Crane is checked against the one in use. *)
let runtime_root () = Option.map Filename.dirname (runtime_include ())

(** The compiler's identity: what [clang++ --version] prints (its version,
    target and installation directory). *)
let compiler () =
  match Subprocess.capture "clang++" ["--version"] with
  | {status = Unix.WEXITED 0; stdout; _} -> String.trim stdout
  | _ | (exception _) -> "unknown"

let env_flags () = Option.default "" (Sys.getenv_opt "CRANE_BAKE_FLAGS")

(** The prerequisites a Make-style dependency file ([clang -MD]) lists: every
    path after a target's colon, with line continuations and escaped spaces. *)
let parse_depfile text =
  let n = String.length text in
  let paths = ref [] and cur = Buffer.create 64 and after_colon = ref false in
  let flush () =
    if Buffer.length cur > 0 then begin
      if !after_colon then paths := Buffer.contents cur :: !paths;
      Buffer.clear cur
    end
  in
  let i = ref 0 in
  while !i < n do
    let c = text.[!i] in
    ( match c with
    | '\\' when !i + 1 < n && text.[!i + 1] = '\n' ->
      flush ();
      incr i
    | '\\' when !i + 1 < n && (text.[!i + 1] = ' ' || text.[!i + 1] = '#') ->
      Buffer.add_char cur text.[!i + 1];
      incr i
    | '$' when !i + 1 < n && text.[!i + 1] = '$' ->
      Buffer.add_char cur '$';
      incr i
    | ':' when (not !after_colon) && (!i + 1 >= n || text.[!i + 1] = ' ' || text.[!i + 1] = '\n') ->
      Buffer.clear cur;
      after_colon := true
    | ' ' | '\t' | '\r' -> flush ()
    | '\n' ->
      flush ();
      after_colon := false
    | c -> Buffer.add_char cur c );
    incr i
  done;
  flush ();
  List.rev !paths

let has_prefix ~dir path =
  let dir = if String.ends_with ~suffix:Filename.dir_sep dir then dir else dir ^ Filename.dir_sep in
  String.starts_with ~prefix:dir path

(** The inputs the dependency files [depfiles] list, but the files under
    [generated] (the extracted unit and the driver, which the Rocq document
    determines): each digested now. *)
let record ~generated depfiles =
  let root = runtime_root () in
  let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p in
  let paths =
    List.concat_map (fun f -> parse_depfile (In_channel.with_open_bin f In_channel.input_all)) depfiles
    |> List.map absolute
    |> List.filter (fun p -> not (has_prefix ~dir:generated p))
    |> List.sort_uniq String.compare
  in
  List.map
    (fun p ->
      let digest = Digest.file p in
      match root with
      | Some root when has_prefix ~dir:root p ->
        let file = String.sub p (String.length root + 1) (String.length p - String.length root - 1) in
        {Base.Table.file; in_runtime = true; digest}
      | _ -> {Base.Table.file = p; in_runtime = false; digest} )
    paths

(** The first of [inputs] that differs from the file it names now (resolving
    a runtime header against [runtime_root]), and how; [digest] digests a file
    (a cache, when several images share headers). *)
let changed_input ?(digest = Digest.file) ~runtime_root inputs =
  List.find_map
    (fun (i : Base.Table.bake_input) ->
      let path =
        if i.in_runtime then Option.map (fun r -> Filename.concat r i.file) runtime_root else Some i.file
      in
      match path with
      | None -> Some (i.file ^ " (Crane's runtime is not found)")
      | Some p when not (Sys.file_exists p) -> Some (p ^ " no longer exists")
      | Some p -> if Digest.equal (digest p) i.digest then None else Some (p ^ " has changed") )
    inputs

(** Refuses an extraction that would emit a stale image: one of [baked]
    whose inputs are not what they were when it was baked. *)
let check (baked : (GlobRef.t * Base.Table.baked) list) =
  if baked <> [] then begin
    let digests = Hashtbl.create 64 in
    let digest p =
      match Hashtbl.find_opt digests p with
      | Some d -> d
      | None ->
        let d = Digest.file p in
        Hashtbl.add digests p d;
        d
    in
    let runtime_root = runtime_root () in
    let compiler = lazy (compiler ()) in
    List.iter
      (fun (r, (b : Base.Table.baked)) ->
        let stale =
          match changed_input ~digest ~runtime_root b.inputs with
          | Some what -> Some what
          | None ->
            if not (String.equal b.env_flags (env_flags ())) then Some "CRANE_BAKE_FLAGS has changed"
            else if not (String.equal b.compiler (Lazy.force compiler)) then
              Some "the compiler (clang++ --version) has changed"
            else None
        in
        match stale with
        | None -> ()
        | Some what ->
          CErrors.user_err
            Pp.(
              str "Crane Bake: the baked image of " ++ Printer.pr_global r ++ str " is stale: " ++ str what
              ++ str " since it was baked." ++ spc ()
              ++ strbrk "Rebuild the file whose Crane Bake command baked it." ) )
      baked
  end
