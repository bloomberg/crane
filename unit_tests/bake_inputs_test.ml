(* A baked image's inputs: the dependency file the bake driver's compiler
   writes, and the check that refuses an image whose inputs have changed. *)

open Crane_plugin

let check name cond =
  if not cond then (
    Printf.eprintf "bake_inputs: %s\n" name;
    exit 1 )

let () =
  let parse = Driver.Bake_inputs.parse_depfile in
  check "continuations and escaped spaces"
    (parse "out/exe: b.cpp \\\n  /usr/include/c++/v1/string \\\n  /a\\ b/x.h\n"
    = ["b.cpp"; "/usr/include/c++/v1/string"; "/a b/x.h"]);
  check "two rules" (parse "a.o: a.cpp a.h\nb.o: b.cpp\n" = ["a.cpp"; "a.h"; "b.cpp"]);
  check "no prerequisites" (parse "a.o:\n" = []);
  (* A runtime header and another file, recorded; then each changed. *)
  let root = Filename.temp_dir "bake_inputs" "" in
  Sys.mkdir (Filename.concat root "cpp") 0o755;
  let write path text = Out_channel.with_open_bin path (fun oc -> output_string oc text) in
  let header = Filename.concat (Filename.concat root "cpp") "crane_bake.h" in
  let other = Filename.concat root "mapping.h" in
  write header "// v1\n";
  write other "// m1\n";
  let inputs =
    [ {Base.Table.file = "cpp/crane_bake.h"; in_runtime = true; digest = Digest.file header};
      {Base.Table.file = other; in_runtime = false; digest = Digest.file other} ]
  in
  let changed ?(runtime_root = Some root) () = Driver.Bake_inputs.changed_input ~runtime_root inputs in
  check "unchanged" (changed () = None);
  write header "// v2\n";
  check "runtime header changed" (changed () = Some (header ^ " has changed"));
  write header "// v1\n";
  check "restored" (changed () = None);
  (* The runtime moved, with the same headers: still fresh. *)
  let moved = Filename.temp_dir "bake_inputs_moved" "" in
  Sys.mkdir (Filename.concat moved "cpp") 0o755;
  write (Filename.concat (Filename.concat moved "cpp") "crane_bake.h") "// v1\n";
  check "runtime moved" (changed ~runtime_root:(Some moved) () = None);
  write other "// m2\n";
  check "other file changed" (changed () = Some (other ^ " has changed"));
  Sys.remove other;
  check "other file removed" (changed () = Some (other ^ " no longer exists"));
  print_endline "bake_inputs: ok"
