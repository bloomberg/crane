(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Inline mappings' replacement text, classified and instantiated
    ({!Grammar.Foreign}). *)

include Grammar.Foreign

(** [shape_of_text s] is what the replacement text [s] does with its
    arguments: [%a0] is its one argument, unchanged; a text reading the
    [first] or [second] member of its one argument projects a pair. *)
let shape_of_text s =
  if String.equal s "%a0" then Identity
  else
    match Foreign_template.pair_projection_field s with
    | Some f -> Pair_projection f
    | None -> Other

(** [template_of_text s] is the replacement text [s], classified: a text
    binding [%result] is a block, one with no placeholder a bare callee. *)
let template_of_text s =
  let contains sub =
    let n = String.length s and m = String.length sub in
    let rec at i = i + m <= n && (String.sub s i m = sub || at (i + 1)) in
    at 0
  in
  { text = s;
    form = (if contains "%result" then Block else if String.contains s '%' then Templated else Bare_callee);
    shape = shape_of_text s;
    linear = Foreign_template.mentions_each_arg_once s }

(** [uninstantiated r] is the anomaly for an application of [r]'s mapping
    that places its arguments itself ({!Bare_callee}, {!Templated}) reaching
    a reader of settled declarations -- the printer, or what it names: those
    are instantiated before ({!Cpp_erasure.instantiate_foreign}), so meeting
    one means that pass was not run. *)
let uninstantiated r =
  CErrors.anomaly
    Pp.(str "a mapping's application reached the printer uninstantiated: " ++ Names.GlobRef.print r)
