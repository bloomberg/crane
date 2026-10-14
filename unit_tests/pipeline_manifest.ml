(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The pipeline's pass order, as the stages that run it declare it.  Diffed
   against pipeline_manifest.expected, so a change to the count or order of
   passes is a reviewed change to that file; accept one with
   `dune promote`. *)

let () =
  List.iter
    (fun (stage, names) -> Printf.printf "%s: %s\n" stage (String.concat " " names))
    [ ("core", Crane_plugin.Extract_env.core_pass_names);
      ("plan", Crane_plugin.Extract_env.plan_pass_names);
      ("unit", Crane_plugin.Extract_env.unit_pass_names);
      ("represent", Crane_plugin.Extract_env.represent_pass_names);
      ("layout", Crane_plugin.Extract_env.layout_pass_names);
      ("discover", Crane_plugin.Extract_env.discover_pass_names);
      ("finish", Crane_plugin.Cpp_pipeline.pass_names) ]
