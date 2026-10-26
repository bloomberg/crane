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

(* A unit whose body is [sections], nothing in any other section. *)
let unit_of ?(prologue = []) ?(wrapper_bodies = []) sections =
  { Cpp_ast.forward_declarations = prologue;
    erased_aliases = [];
    concept_prerequisites = [];
    concepts = [];
    hoisted_structs = [];
    lifted_specs = [];
    body = Cpp_ast.seq sections;
    deferred_definitions = [];
    deferred_members = [];
    wrapper_bodies }

(* The text, without whitespace: breaks and separators are formatting. *)
let text ?(templates = []) ?(forwards = []) sections =
  let doc = Cpp_ast.print ~write:(fun _ _ -> Pp.str "?") (Cpp_ast.schedule ~templates ~forwards (unit_of ~prologue:[Pp.str "P"] sections)) in
  String.to_seq (Pp.string_of_ppcmds doc)
  |> Seq.filter (fun c -> not (List.mem c [' '; '\n'; '\t']))
  |> String.of_seq

let top = Cpp_ast.top_level
let struct_named ?(layout = Cpp_ast.Block) name = Cpp_ast.Struct {head = {template = []; name = Pp.str name; base = None}; layout}

let () =
  let unit = [top (Cpp_ast.text (Pp.str "a")); top (leaf ~templates:["T"] "b"); top (leaf ~templates:["T"] "c")] in
  check_text "a template goes in front of the first chunk writing it" (text ~templates:[template "T"] unit) "Pa<T>bc";
  check_text "a template nothing writes is declared nowhere" (text ~templates:[template "U"] unit) "Pabc";
  let nested = [top (Cpp_ast.seq [Cpp_ast.text (Pp.str "s{"); top (leaf ~templates:["T"] "x"); Cpp_ast.text (Pp.str "}")])] in
  check_text "a template goes in front of the innermost chunk" (text ~templates:[template "T"] nested) "Ps{<T>x}";
  let struct_ = struct_named "M" in
  let body = Cpp_ast.module_body m [Cpp_ast.text (Pp.str "y"); Cpp_ast.empty; leaf ~templates:["T"] "z"] in
  let homed = [top (Cpp_ast.module_ struct_ ~fields:(Cpp_ast.text (Pp.str "f")) body)] in
  check_text "a homed template goes in front of the member writing it" (text ~templates:[template ~homed:true "T"] homed) "PstructM{fy<T>z};";
  let inner = ModPath.MPdot (m, Label.make "N") in
  let nested =
    Cpp_ast.module_ struct_
      (Cpp_ast.module_body m
         [ Cpp_ast.text (Pp.str "y");
           Cpp_ast.module_
             (struct_named "N")
             (Cpp_ast.module_body inner [Cpp_ast.text (Pp.str "w"); leaf ~templates:["T"] "z"]) ])
  in
  check_text "a homed template goes in front of the innermost member writing it"
    (text ~templates:[template ~homed:true "T"] [top nested]) "PstructM{ystructN{w<T>z};};";
  let sibling name =
    let mp = ModPath.MPdot (m, Label.make name) in
    Cpp_ast.module_
      (struct_named name)
      (Cpp_ast.module_body mp [leaf ~templates:["T"] "u"; leaf ~templates:["T"] "v"])
  in
  check_text "a homed template goes in front of the first member writing it in each module struct"
    (text ~templates:[template ~homed:true "T"] [top (Cpp_ast.seq [sibling "A"; sibling "B"])]) "PstructA{<T>uv};structB{<T>uv};";
  let out_of_line name =
    Cpp_ast.module_ Out_of_line
      (Cpp_ast.module_body (ModPath.MPdot (m, Label.make name)) [leaf ~templates:["T"] (name ^ "u")])
  in
  check_text "modules defined out of line share the scope a homed template is declared in"
    (text ~templates:[template ~homed:true "T"] [top (Cpp_ast.seq [out_of_line "A"; out_of_line "B"])]) "P<T>AuBu";
  check_text "an unhomed template is declared once"
    (text ~templates:[template "T"] [top (sibling "A"); top (sibling "B")]) "P<T>structA{uv};structB{uv};";
  check_text "an unhomed template written in a member goes at namespace scope" (text ~templates:[template "T"] homed) "P<T>structM{fyz};";
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
    (unit_of [documented]))) in
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
    (raw (Cpp_ast.module_ (struct_named "s") one)) "struct s {\ny;\n};";
  check_text "a struct with no members opens a line all the same"
    (raw (Cpp_ast.module_ (struct_named "s") (Cpp_ast.module_body m []))) "struct s {\n};";
  check_text "a struct laid out on one line has its braces on the line of its head"
    (raw (Cpp_ast.module_ (struct_named ~layout:One_line "s") (Cpp_ast.module_body m []))) "struct s {};";
  check "a struct laid out on one line has no body"
    ( match Cpp_ast.module_ (struct_named ~layout:One_line "s") one with
    | exception Invalid_argument _ -> true
    | _ -> false );
  let head = {Cpp_ast.template = [Typename (Pp.str "A"); Constrained {concept = Pp.str "C<P>"; param = Pp.str "M"}];
              name = Pp.str "s"; base = Some (Pp.str "b<s<A, M>>")} in
  check_text "a struct's head writes its template and the class it derives from"
    (raw (Cpp_ast.module_ (Struct {head; layout = Block}) one))
    "template<typename A, C<P> M>\nstruct s : public b<s<A, M>> {\ny;\n};";
  check_text "a body with no struct of its own writes nothing after its members"
    (raw (Cpp_ast.module_ In_enclosing_scope one)) "y;";
  check "no chunk at namespace scope is a struct's member"
    ( match Cpp_ast.module_ struct_ (Cpp_ast.module_body m [top (leaf "x")]) with
    | exception Invalid_argument _ -> true
    | _ -> false );
  check "a chunk at namespace scope may be a member of a body defined out of line"
    (not (Cpp_ast.is_empty (Cpp_ast.module_ Out_of_line (Cpp_ast.module_body m [top (leaf "x")]))));
  check "an empty chunk is no chunk" (Cpp_ast.is_empty (top Cpp_ast.empty));
  check "a declaration needing something is not empty" (not (Cpp_ast.is_empty (leaf ~templates:["T"] "")));
  let unprinted ?templates () =
    Cpp_ast.unprinted ~needs:(needs ?templates ()) (Common.empty_env ())
      (Cpp_erasure.materialise (Minicpp.Dstatic_assert (Minicpp.CPPbool true, None)))
  in
  let spelled ?(templates = []) sections =
    let write spelling (_ : Cpp_ast.unprinted) =
      Pp.str
        ( match spelling with
        | Cpp_ast.Element_of mp -> "E(" ^ ModPath.to_string mp ^ ")"
        | Member_of mp -> "M(" ^ ModPath.to_string mp ^ ")" )
    in
    Pp.string_of_ppcmds (Cpp_ast.print ~write (Cpp_ast.schedule ~templates ~forwards:[] (unit_of sections)))
  in
  check_text "a declaration not yet printed is spelled as an element of the module of the group around it"
    (spelled [top (Cpp_ast.elements ~source:m (unprinted ()))]) "E(F.M)";
  check_text "the innermost struct around a declaration not yet printed spells it as its member"
    (spelled [top (Cpp_ast.elements ~source:m (Cpp_ast.module_ struct_ (Cpp_ast.module_body inner [unprinted ()])))])
    "struct M {\nM(F.M.N)\n};";
  check_text "the innermost group around a declaration not yet printed spells it"
    (spelled [top (Cpp_ast.module_ struct_ (Cpp_ast.module_body m [Cpp_ast.elements ~source:inner (unprinted ())]))])
    "struct M {\nE(F.M.N)\n};";
  let fields ?templates () =
    Cpp_ast.fields ~needs:(needs ?templates ()) ~record:(GlobRef.VarRef (Id.of_string "r")) ~vars:[] []
  in
  check_text "a struct's fields written as elements of the module around it are spelled as its elements"
    (spelled
       [ top
           (Cpp_ast.elements ~source:m
              (Cpp_ast.module_ struct_ ~fields:(Cpp_ast.elements ~source:m (fields ())) (Cpp_ast.module_body inner [unprinted ()])) ) ])
    "struct M {\nE(F.M)M(F.M.N)\n};";
  check_text "a homed template a struct's fields write goes in front of the member holding the struct"
    (text ~templates:[template ~homed:true "T"]
       [ top
           (Cpp_ast.module_ struct_
              (Cpp_ast.module_body m
                 [ Cpp_ast.text (Pp.str "y");
                   Cpp_ast.module_
                     (struct_named "N")
                     ~fields:(Cpp_ast.elements ~source:m (fields ~templates:["T"] ()))
                     (Cpp_ast.module_body inner [leaf "w"]) ]) ) ])
    "PstructM{y<T>structN{?w};};";
  check_text "a declaration not yet printed is placed by what it needs, as planned"
    (spelled ~templates:[template "T"] [top (Cpp_ast.elements ~source:m (unprinted ~templates:["T"] ()))])
    "<T>E(F.M)";
  let refused sections = match spelled sections with exception Invalid_argument _ -> true | _ -> false in
  check "a declaration not yet printed outside every group and struct is refused" (refused [top (unprinted ())]);
  check "a body defined out of line does not say how a declaration in it is spelled"
    (refused [top (Cpp_ast.module_ Out_of_line (Cpp_ast.module_body m [unprinted ()]))]);
  check "a declaration not yet printed is not empty" (not (Cpp_ast.is_empty (unprinted ())));
  let joined_as printed =
    let l = [leaf "x;"; Cpp_ast.empty; Cpp_ast.elements ~source:m (unprinted ())] in
    Pp.string_of_ppcmds
      (Cpp_ast.print ~write:(fun _ _ -> Pp.str printed)
         (Cpp_ast.schedule ~templates:[] ~forwards:[] (unit_of [Cpp_ast.joined l])) )
  in
  check_text "a joined declaration printed opening a doc comment follows a newline" (joined_as "/// d") "x;\n/// d";
  check "any other joined declaration follows a break"
    (let s = joined_as "d" in String.starts_with ~prefix:"x;" s && String.ends_with ~suffix:"d" s && not (String.contains s '\n'));
  check "nothing joined is nothing" (Cpp_ast.is_empty (Cpp_ast.joined [Cpp_ast.empty; Cpp_ast.empty]));
  check_text "one thing joined is that thing" (raw (Cpp_ast.joined [Cpp_ast.empty; leaf "x;"])) "x;";
  let t s = Cpp_ast.text (Pp.str s) in
  let full =
    { Cpp_ast.forward_declarations = [Pp.str "f1"; Pp.str "f2"];
      erased_aliases = [t "e1"; t "e2"];
      concept_prerequisites = [t "p"];
      concepts = [t "c1"; Cpp_ast.empty; t "c2"];
      hoisted_structs = [t "h"];
      lifted_specs = [Cpp_ast.empty];
      body = t "b";
      deferred_definitions = [t "d1"; Cpp_ast.empty; t "d2"];
      deferred_members = [t "m"];
      wrapper_bodies = [] }
  in
  let printed u = Pp.string_of_ppcmds (Cpp_ast.print ~write:(fun _ _ -> Pp.str "?") (Cpp_ast.schedule ~templates:[] ~forwards:[] u)) in
  let squeezed u = String.of_seq (Seq.filter (fun c -> not (List.mem c [' '; '\n'])) (String.to_seq (printed u))) in
  check_text "a unit writes its forward declarations, then its sections in order, skipping empty groups"
    (squeezed full) "f1f2e1e2pc1c2hbd1d2m";
  check "erased aliases are separated by a line break"
    (let s = printed {full with forward_declarations = []; concept_prerequisites = []; concepts = []; hoisted_structs = []; body = Cpp_ast.empty;
                     deferred_definitions = []; deferred_members = []} in
     String.starts_with ~prefix:"e1\ne2" s);
  check "a unit with nothing in it writes nothing" (printed (unit_of []) = "");
  let group position = raw (Cpp_ast.concept_group position [t "c1"; t "c2"]) in
  check_text "classes' concepts ahead of a struct follow a line break" (group Classes_ahead) "\nc1\nc2\n\n";
  check_text "module types' concepts ahead of a struct follow nothing" (group Module_types_ahead) "c1\nc2\n\n";
  check_text "concepts after a struct follow a blank line" (group After_struct) "\n\nc1\nc2\n\n";
  check "no concepts are no group" (Cpp_ast.is_empty (Cpp_ast.concept_group After_struct []));
  let wrapper = Cpp_ast.wrapper_struct ~name:"W" ~module_:inner ~fields:(t "f;") in
  let filled bodies = Pp.string_of_ppcmds (Cpp_ast.print ~write:(fun _ _ -> Pp.str "?")
      (Cpp_ast.schedule ~templates:[template ~homed:true "T"] ~forwards:[] (unit_of ~wrapper_bodies:bodies [top wrapper]))) in
  check_text "a wrapper struct is filled in with its module's body, after its own members"
    (filled [("W", Cpp_ast.module_body inner [t "y;"; leaf ~templates:["T"] "z;"])])
    "struct W {\nf;y;<T>z;\n};";
  let refused_fill bodies = match filled bodies with exception Invalid_argument _ -> true | _ -> false in
  check "a wrapper struct with no body is refused" (refused_fill []);
  check "a wrapper struct given another module's body is refused" (refused_fill [("W", Cpp_ast.module_body m [t "y;"])]);
  check "a wrapper struct is a struct its module declares"
    (match Cpp_ast.declared wrapper with [Struct_of mp] -> ModPath.equal mp inner | _ -> false);
  check "the wrapper structs of a tree are listed in the order written"
    (Cpp_ast.wrapper_structs (Cpp_ast.seq [wrapper; top (Cpp_ast.wrapper_struct ~name:"V" ~module_:m ~fields:Cpp_ast.empty)]) = ["W"; "V"]);
  check "a wrapper struct not filled in is not printed"
    (match Cpp_ast.to_pp wrapper with exception Invalid_argument _ -> true | _ -> false);
  let spelling_text = function Cpp_ast.Element_of mp -> "E(" ^ ModPath.to_string mp ^ ")" | Member_of mp -> "M(" ^ ModPath.to_string mp ^ ")" in
  let resolve spelling mp = Cpp_name.unqualified (ModPath.to_string mp ^ "@" ^ spelling_text spelling) in
  let resolved_text sections =
    let write spelling (u : Cpp_ast.unprinted) =
      match u.declaration with
      | Module_alias {target = Module_named {name = Resolved n; _}; _} -> Pp.str (spelling_text spelling ^ "=" ^ Cpp_name.to_string n)
      | Module_alias {target = Module_named {name = Unresolved; _}; _} -> Pp.str "unresolved"
      | _ -> Pp.str (spelling_text spelling)
    in
    Pp.string_of_ppcmds (Cpp_ast.print_tree ~write (Cpp_ast.resolve_tree ~resolve (Cpp_ast.seq sections)))
  in
  check_text "resolving keeps how each declaration is spelled"
    (resolved_text [top (Cpp_ast.elements ~source:m (unprinted ()))]) "E(F.M)";
  let alias = Cpp_ast.module_alias ~name:(Pp.str "A") (Module_named (Cpp_ast.module_ref inner)) in
  check_text "a module a declaration names is resolved where the declaration is written"
    (resolved_text [top (Cpp_ast.elements ~source:m (Cpp_ast.module_ struct_ (Cpp_ast.module_body inner [alias])))])
    "struct M {\nM(F.M.N)=F.M.N@M(F.M.N)\n};";
  check_text "a module a declaration names is unresolved until resolved"
    (Pp.string_of_ppcmds
       (Cpp_ast.print_tree
          ~write:(fun _ (u : Cpp_ast.unprinted) ->
            match u.declaration with Module_alias {target = Module_named {name = Unresolved; _}; _} -> Pp.str "u" | _ -> Pp.str "r")
          (Cpp_ast.elements ~source:m alias) ))
    "u"
