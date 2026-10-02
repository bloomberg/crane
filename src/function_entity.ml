(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

type t = {declaration : cpp_decl; definition : cpp_decl}

let rec finalize (d : cpp_decl) : t option =
  match d with
  | Dfun ({df_shape = Ddef (params, body); _} as f) ->
    let no_pure =
      f.df_no_pure
      || match body with [Sreturn (Some (CPPabort _))] -> true | _ -> false
    in
    let f = {f with df_no_pure = no_pure} in
    Some
      { declaration =
          Dfun
            { f with
              df_shape = Ddecl (List.map (fun (id, ty) -> (Some id, ty)) params) };
        definition = Dfun f }
  | Dtemplate (temps, cstr, inner) ->
    Option.map
      (fun e ->
        let temps =
          match inner with
          | Dfun {df_shape = Ddef (params, body); _} ->
            drop_stored_callback_constraints ~params body temps
          | _ -> temps
        in
        { declaration = Dtemplate (temps, cstr, e.declaration);
          definition = Dtemplate (temps, cstr, e.definition) } )
      (finalize inner)
  | _ -> None

let declaration e = e.declaration
let definition e = e.definition

let declaration_of d =
  match finalize d with Some e -> e.declaration | None -> d
