(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the template parameters of a generated inductive or alias are, by
    0-based position in its C++ template parameter list.  Recorded by
    [Gen_decls.hkt_templates] when the declaration's header is generated, and
    read back wherever a use of the declaration is converted.

    It lives below {!Table} so that {!Minicpp} can ask it directly: rebuilding
    an application ([Minicpp.map_cpp_type]) has to know whether its head is
    parameterised by a family, and that used to be a hook {!Table} installed
    into {!Minicpp} at load time. *)

open Names

(* Positions declared [template <typename> class], each with its arity. *)
let template_template : (GlobRef.t, (int * int) list) Hashtbl.t =
  Hashtbl.create 16

(* Positions applied in the definition but still declared a plain [typename]:
   event families, applied only at indices, whose argument is the family's
   own struct. *)
let family : (GlobRef.t, int list) Hashtbl.t = Hashtbl.create 16

(* Positions the definition never spells -- an erased event family -- so no
   instantiation may be written in them at a use. *)
let phantom : (GlobRef.t, int list) Hashtbl.t = Hashtbl.create 16

let reset () =
  Hashtbl.reset template_template;
  Hashtbl.reset family;
  Hashtbl.reset phantom

let sizes () =
  [ ("hkt_ind_params", Hashtbl.length template_template);
    ("phantom_type_params", Hashtbl.length phantom) ]

let record tbl r positions = if positions <> [] then Hashtbl.replace tbl r positions

let add_template_template r = record template_template r

let template_template_arity r i =
  match Hashtbl.find_opt template_template r with
  | Some s -> List.assoc_opt i s
  | None -> None

let add_family r = record family r

let is_family r i =
  match Hashtbl.find_opt family r with Some l -> List.mem i l | None -> false

let has_family r = Hashtbl.mem family r

let add_phantom r = record phantom r

let is_phantom r i =
  match Hashtbl.find_opt phantom r with Some l -> List.mem i l | None -> false
