(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the template parameters of a generated inductive or alias are, by
    0-based position in its C++ template parameter list.  Planned before
    anything is rendered and recorded again by [Plan_templates.hkt_templates]
    when the declaration's header is generated; read back wherever a use of
    the declaration is converted.

    It lives below {!Table} so that {!Minicpp} can ask it directly: rebuilding
    an application ([Minicpp.map_cpp_type]) has to know whether its head is
    parameterised by a family, and that used to be a hook {!Table} installed
    into {!Minicpp} at load time. *)

type t = {
  template_templates : (int * int) list;
  families : int list;
  phantoms : int list;
}

let equal a b =
  List.equal (fun (i, n) (j, m) -> Int.equal i j && Int.equal n m) a.template_templates b.template_templates
  && List.equal Int.equal a.families b.families
  && List.equal Int.equal a.phantoms b.phantoms

(* Positions declared [template <typename> class], each with its arity. *)
let template_template : (int * int) list Ref.User.Tbl.t = Ref.User.Tbl.create 16

(* Positions applied in the definition but still declared a plain [typename]:
   event families, applied only at indices, whose argument is the family's
   own struct. *)
let family : int list Ref.User.Tbl.t = Ref.User.Tbl.create 16

(* Positions the definition never spells -- an erased event family -- so no
   instantiation may be written in them at a use. *)
let phantom : int list Ref.User.Tbl.t = Ref.User.Tbl.create 16

let reset () =
  Ref.User.Tbl.reset template_template;
  Ref.User.Tbl.reset family;
  Ref.User.Tbl.reset phantom

let sizes () =
  [ ("hkt_ind_params", Ref.User.Tbl.length template_template);
    ("phantom_type_params", Ref.User.Tbl.length phantom) ]

let record_in tbl r positions = if positions <> [] then Ref.User.Tbl.replace tbl r positions

let record r k =
  record_in template_template r k.template_templates;
  record_in family r k.families;
  record_in phantom r k.phantoms

let recorded r =
  let find tbl = Option.default [] (Ref.User.Tbl.find_opt tbl r) in
  {template_templates = find template_template; families = find family; phantoms = find phantom}

let template_template_arity r i =
  match Ref.User.Tbl.find_opt template_template r with
  | Some s -> List.assoc_opt i s
  | None -> None

let is_family r i =
  match Ref.User.Tbl.find_opt family r with Some l -> List.mem i l | None -> false

let has_family r = Ref.User.Tbl.mem family r

let is_phantom r i =
  match Ref.User.Tbl.find_opt phantom r with Some l -> List.mem i l | None -> false
