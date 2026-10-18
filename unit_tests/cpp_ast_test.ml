(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Where a translation unit's due declarations go, read off the tree alone:
   a template in front of the innermost chunk first writing it, or, homed,
   of the innermost member of a module first writing it; a constrained
   forward declaration in front of the chunk first naming its struct,
   unless that chunk defines it. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "cpp_ast: %s\n" name;
    exit 1 )

let check_text name got expected =
  if not (String.equal got expected) then (
    Printf.eprintf "cpp_ast: %s: got %S, expected %S\n" name got expected;
    exit 1 )

let m = ModPath.MPdot (ModPath.MPfile (DirPath.make [Id.of_string "F"]), Label.make "M")
let needs ?(templates = []) ?(names = []) ?(defines = []) () = {Cpp_ast.Needs.templates; names; defines}
let leaf ?templates ?names ?defines s = Cpp_ast.decl ~needs:(needs ?templates ?names ?defines ()) (Pp.str s)
let template ?(homed = false) ?(holder = false) name = {Cpp_ast.name; homed; holder; declaration = Pp.str ("<" ^ name ^ ">")}
let forward s = {Cpp_ast.struct_ = s; forward_declaration = Pp.str ("fwd:" ^ s)}

(* The text, without whitespace: breaks and separators are formatting. *)
let text ?(templates = []) ?(forwards = []) sections =
  let doc = Cpp_ast.print ~write:(fun _ _ -> Pp.str "?") (Cpp_ast.schedule ~templates ~forwards {prologue = Pp.str "P"; sections}) in
  String.to_seq (Pp.string_of_ppcmds doc)
  |> Seq.filter (fun c -> not (List.mem c [' '; '\n'; '\t']))
  |> String.of_seq

let top = Cpp_ast.top_level

let () =
  let unit = [top (Cpp_ast.text (Pp.str "a")); top (leaf ~templates:["T"] "b"); top (leaf ~templates:["T"] "c")] in
  check_text "a template goes in front of the first chunk writing it" (text ~templates:[template "T"] unit) "Pa<T>bc";
  check_text "a template nothing writes is declared nowhere" (text ~templates:[template "U"] unit) "Pabc";
  let nested = [top (Cpp_ast.seq [Cpp_ast.text (Pp.str "s{"); top (leaf ~templates:["T"] "x"); Cpp_ast.text (Pp.str "}")])] in
  check_text "a template goes in front of the innermost chunk" (text ~templates:[template "T"] nested) "Ps{<T>x}";
  let struct_ = Cpp_ast.Struct {head = Pp.str "struct-M{"; tail = Pp.str "}"} in
  let body = Cpp_ast.module_body m [Cpp_ast.text (Pp.str "y"); Cpp_ast.empty; leaf ~templates:["T"] "z"] in
  let homed = [top (Cpp_ast.module_ struct_ ~fields:(Cpp_ast.text (Pp.str "f")) body)] in
  check_text "a homed template goes in front of the member writing it" (text ~templates:[template ~homed:true "T"] homed) "Pstruct-M{fy<T>z}";
  let inner = ModPath.MPdot (m, Label.make "N") in
  let nested =
    Cpp_ast.module_ struct_
      (Cpp_ast.module_body m
         [ Cpp_ast.text (Pp.str "y");
           Cpp_ast.module_
             (Struct {head = Pp.str "struct-N{"; tail = Pp.str "}"})
             (Cpp_ast.module_body inner [Cpp_ast.text (Pp.str "w"); leaf ~templates:["T"] "z"]) ])
  in
  check_text "a homed template goes in front of the innermost member writing it"
    (text ~templates:[template ~homed:true "T"] [top nested]) "Pstruct-M{ystruct-N{w<T>z}}";
  let sibling name =
    let mp = ModPath.MPdot (m, Label.make name) in
    Cpp_ast.module_
      (Struct {head = Pp.str (name ^ "{"); tail = Pp.str "}"})
      (Cpp_ast.module_body mp [leaf ~templates:["T"] "u"; leaf ~templates:["T"] "v"])
  in
  check_text "a homed template goes in front of the first member writing it in each module struct"
    (text ~templates:[template ~homed:true "T"] [top (Cpp_ast.seq [sibling "A"; sibling "B"])]) "PA{<T>uv}B{<T>uv}";
  let out_of_line name =
    Cpp_ast.module_ Out_of_line
      (Cpp_ast.module_body (ModPath.MPdot (m, Label.make name)) [leaf ~templates:["T"] (name ^ "u")])
  in
  check_text "modules defined out of line share the scope a homed template is declared in"
    (text ~templates:[template ~homed:true "T"] [top (Cpp_ast.seq [out_of_line "A"; out_of_line "B"])]) "P<T>AuBu";
  check_text "an unhomed template is declared once"
    (text ~templates:[template "T"] [top (sibling "A"); top (sibling "B")]) "P<T>A{uv}B{uv}";
  check_text "an unhomed template written in a member goes at namespace scope" (text ~templates:[template "T"] homed) "P<T>struct-M{fyz}";
  check_text "a homed template goes in front of its home's member defined out of line"
    (text ~templates:[template ~homed:true "T"] [top (Cpp_ast.module_ Out_of_line body)]) "Py<T>z";
  check "a struct with no members is written" (not (Cpp_ast.is_empty (Cpp_ast.module_ struct_ (Cpp_ast.module_body m []))));
  check "a body with no members and no struct writes nothing"
    (Cpp_ast.is_empty (Cpp_ast.module_ In_enclosing_scope (Cpp_ast.module_body m [Cpp_ast.empty])));
  let documented =
    Cpp_ast.module_ In_enclosing_scope
      (Cpp_ast.module_body m [Cpp_ast.text (Pp.str "y;"); leaf ~templates:["T"] "/// z"])
  in
  let printed = Pp.string_of_ppcmds (Cpp_ast.print ~write:(fun _ _ -> Pp.str "?") (Cpp_ast.schedule ~templates:[template ~homed:true "T"] ~forwards:[]
    {prologue = Pp.mt (); sections = [documented]})) in
  check_text "a member opening with a doc comment follows a newline, whatever is due in front of it"
    (String.sub printed 0 6) "y;\n<T>";
  check_text "holders go in front of aliases, each in the order given" (text
        ~templates:[template "A"; template ~holder:true "H"; template "B"]
        [top (leaf ~templates:["B"; "A"; "H"] "d")]) "P<H><A><B>d";
  let fwd = [top (leaf ~names:["S"] "e"); top (leaf ~names:["S"] ~defines:["S"] "f")] in
  check_text "a forward declaration goes in front of the first chunk naming its struct" (text ~forwards:[forward "S"] fwd) "Pfwd:Sef";
  check_text "no forward declaration is due where the first chunk naming the struct defines it" (text ~forwards:[forward "S"] (List.rev fwd)) "Pfe";
  check_text "forward declarations go in front of templates" (text ~templates:[template "T"] ~forwards:[forward "S"] [top (leaf ~templates:["T"] ~names:["S"] "g")]) "Pfwd:S<T>g";
  let raw t = Pp.string_of_ppcmds (Cpp_ast.to_pp t) in
  let one = Cpp_ast.module_body m [Cpp_ast.text (Pp.str "y;")] in
  check_text "a struct closes its members on a line of its own"
    (raw (Cpp_ast.module_ (Struct {head = Pp.str "s{"; tail = Pp.str "}"}) one)) "s{y;\n}";
  check_text "a body with no struct of its own writes nothing after its members"
    (raw (Cpp_ast.module_ In_enclosing_scope one)) "y;";
  check "no chunk at namespace scope is a struct's member"
    ( match Cpp_ast.module_ struct_ (Cpp_ast.module_body m [top (leaf "x")]) with
    | exception Invalid_argument _ -> true
    | _ -> false );
  check "a chunk at namespace scope may be a member of a body defined out of line"
    (not (Cpp_ast.is_empty (Cpp_ast.module_ Out_of_line (Cpp_ast.module_body m [top (leaf "x")]))));
  check "an empty chunk is no chunk" (Cpp_ast.is_empty (top Cpp_ast.empty));
  check "a declaration needing something is not empty" (not (Cpp_ast.is_empty (leaf ~templates:["T"] "")))
