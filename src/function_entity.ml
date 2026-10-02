(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


type t = {
  declaration : Cpp_erasure.settled;
  definition : Cpp_erasure.settled;
  defines_function : bool;
}

let of_finished d =
  match Cpp_erasure.split_definition d with
  | Some (declaration, definition) ->
    {declaration; definition; defines_function = true}
  | None -> {declaration = d; definition = d; defines_function = false}

let finalize d = of_finished (Cpp_pipeline.finish d)
let finalize_group ds = List.map of_finished (Cpp_pipeline.finish_group ds)
let declaration e = e.declaration
let definition e = e.definition
let defines_function e = e.defines_function
