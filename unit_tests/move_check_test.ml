(* The moved-value validator on reuse arms: a token is consumed once, and
   nothing reads its local after; what was taken out of the local before
   is not read of it. *)

open Names
open Crane_plugin

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

let id = Id.of_string
let mk_call = Cpp_ir.Build.call
let v x : expr = Local (id x)
let tree : ty = Entity_application (GlobRef.VarRef (id "tree"), [], [])

(* [tree::node_crane_reuse(args)], the token first. *)
let reuse args = mk_call (Type_member (tree, Base.Generated_name.companion (id "node") "reuse")) args

(* [std::get<tree::Node>(t.v_mut())], the alternative [t] holds. *)
let alternative t : expr = Variant_get (Member (tree, id "Node"), Some (mk_call (Access (Dot, v t, id "v_mut")) []))

(* [std::get<tree::Node>(t.v_mut()).f], a field of the alternative [t] holds. *)
let field t f : expr = Access (Dot, alternative t, id f)

(* [%a0.first] applied to [pair], instantiated (a foreign call). *)
let projection f pair : expr =
  Foreign
    ( Call,
      { custom = GlobRef.VarRef (id f);
        types = [];
        values = [pair];
        yields = None;
        pieces = [Value 0; Text ("." ^ f)] } )

(* A frame pushed onto a stack, as a loop saving its continuation does. *)
let push args = mk_call (Access (Dot, v "_stack", id "push_back")) [Braced args]

(* A match on [t] whose one branch binds [fields] into it. *)
let match_ t fields body : stmt =
  let binding x : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Match.field_binding =
    {name = id x; type_ = Auto; used = true; binder = None}
  in
  Match
    ( {expr = mk_call (Access (Dot, v t, id "v_mut")) []; access = Dot; owned = true; flat = false},
      [ { ctor_type = Member (tree, id "Node");
          var = None;
          field_bindings = List.map binding fields;
          extra_conditions = [];
          body } ],
      None )

let check name body expected =
  let found = List.map Id.to_string (Ownership_ir.Move_check.moved_reads body) in
  if found <> expected then (
    Printf.eprintf "move_check: %s: found [%s]\n" name (String.concat "; " found);
    exit 1 )

let decl x e : stmt = Bind_variable (id x, Declare (Auto, None), e)

let () =
  check "fields taken out, then the storage"
    [ decl "l" (Move (Dereference (field "t" "a0")));
      decl "k" (Move (field "t" "a1"));
      Return (Some (reuse [Move (v "t"); Move (v "l"); v "k"])) ]
    [];
  check "the token consumed twice"
    [ Expression (reuse [Move (v "t"); v "k"]);
      Return (Some (reuse [Move (v "t"); v "k"])) ]
    ["t"];
  check "the local read after its storage is rebuilt"
    [ decl "n" (reuse [Move (v "t"); v "k"]);
      Return (Some (mk_call (Access (Dot, v "t", id "v")) [])) ]
    ["t"];
  check "the local read beside its token"
    [Return (Some (reuse [Move (v "t"); mk_call (Access (Dot, v "t", id "v")) []]))]
    ["t"];
  check "a child cell handed over, then read"
    [ decl "xs" (Move (Dereference (field "t" "a1")));
      decl "n" (reuse [Move (field "t" "a1"); v "xs"]);
      Return (Some (field "t" "a1")) ]
    ["t"];
  check "a child cell handed over, a sibling field read"
    [ decl "n" (reuse [Move (field "t" "a1"); Move (field "t" "a0")]);
      Return (Some (v "n")) ]
    [];
  check "the local assigned afresh after its storage is rebuilt"
    [ decl "n" (reuse [Move (v "t"); v "k"]);
      Bind_variable (id "t", Existing, v "n");
      Return (Some (v "t")) ]
    [];
  check "a field read through a binding after its local is moved"
    [ Structured_binding ([id "a0"; id "a1"], alternative "t");
      Expression (push [Move (v "t")]);
      Expression (push [v "a0"]) ]
    ["t"];
  check "a field read through a binding beside a move of its local"
    [Structured_binding ([id "a0"], alternative "t"); Expression (push [Move (v "t"); v "a0"])]
    ["t"];
  check "a local copied, then a field moved out of it, in one initialiser"
    [Structured_binding ([id "a0"], alternative "t"); Expression (push [v "t"; Move (v "a0")])]
    [];
  check "a local moved and a field read in a call's arguments"
    [Structured_binding ([id "a0"], alternative "t"); Expression (mk_call (v "f") [v "t"; Move (v "a0")])]
    ["t"];
  check "a field moved out through a binding, then the storage"
    [ Structured_binding ([id "a0"; id "a1"], alternative "t");
      decl "l" (Move (v "a0"));
      Return (Some (reuse [Move (v "t"); Move (v "l")])) ]
    [];
  check "a field handed over through a binding beside its storage"
    [Structured_binding ([id "a0"], alternative "t"); Return (Some (reuse [Move (v "t"); Move (v "a0")]))]
    ["t"];
  check "two bindings into one local, one moved and the other read"
    [Structured_binding ([id "a0"; id "a1"], alternative "t"); Expression (push [Move (v "a0")]);
      Return (Some (v "a1"))]
    [];
  check "a binding into a computed value"
    [ Structured_binding ([id "a0"], mk_call (v "f") [v "t"]);
      Expression (push [Move (v "t")]);
      Return (Some (v "a0")) ]
    [];
  check "a match's field read after its scrutinee is moved"
    [match_ "t" ["a0"] [Expression (push [Move (v "t")]); Return (Some (v "a0"))]]
    ["t"];
  check "a match's field read after a binding of the same name"
    [match_ "t" ["a0"]
      [Structured_binding ([id "a0"], mk_call (v "f") []); Expression (push [Move (v "t")]); Return (Some (v "a0"))]]
    [];
  check "a reference declared to a field, read after its local is moved"
    [ Bind_variable (id "r", Declare (Reference (Lvalue, Auto), None), field "t" "a0");
      Expression (push [Move (v "t")]);
      Return (Some (v "r")) ]
    ["t"];
  check "a copy of a field, read after its local is moved"
    [decl "c" (field "t" "a0"); Expression (push [Move (v "t")]); Return (Some (v "c"))]
    [];
  check "each component taken out of a pair through its instantiated projection"
    [Expression (push [projection "first" (Move (v "p")); projection "second" (Move (v "p"))])]
    []

(* A callable's parameters and body against the convention its plan
   states: [f] owns [a] and lends [b]. *)
let () =
  let f = GlobRef.VarRef (id "f") in
  let decided =
    Core_plan.Callable_abi.decide
      ~callables:[Core_plan.Callable_abi.of_head ~passing:[Owned; Borrowed] ~callee:f ~scheme:None []]
      ~assumed:[] ~instance_methods:[]
  in
  let cref : ty = Reference (Lvalue, Const tree) in
  let convention name params body expected =
    let found = Option.map List.length (Ownership_ir.Move_check.convention_violations decided f params body) in
    if found <> Some expected then (
      Printf.eprintf "move_check: %s: %s violations, expected %d\n" name
        (match found with Some n -> string_of_int n | None -> "no plan's") expected;
      exit 1 )
  in
  convention "as the plan has them" [(id "a", tree); (id "b", cref)]
    [Return (Some (mk_call (v "g") [Move (v "a"); v "b"]))] 0;
  convention "an owned parameter declared by reference" [(id "a", cref); (id "b", cref)] [] 1;
  convention "a lent parameter moved out of" [(id "a", tree); (id "b", cref)] [Return (Some (Move (v "b")))] 1;
  convention "a lent parameter's name declared again and moved"
    [(id "a", tree); (id "b", cref)]
    [decl "b" (v "a"); Return (Some (Move (v "b")))]
    0;
  convention "a parameter the plan does not pass" [(id "a", tree)] [] 1;
  if Ownership_ir.Move_check.convention_violations decided (GlobRef.VarRef (id "unplanned")) [] [] <> None then (
    prerr_endline "move_check: a callable with no plan has a convention";
    exit 1 )

(* A reference bound into a local is not read after the local is given a
   new value: the storage it names is gone.  A pointer local given a new
   value leaves what it pointed at; a reference bound after the assignment
   names the new value. *)
let () =
  let stale name body expected =
    let found = List.map (fun (a, b) -> Id.to_string a ^ "@" ^ Id.to_string b) (Ownership_ir.Move_check.stale_references body) in
    if found <> expected then (
      Printf.eprintf "move_check: %s: stale [%s]\n" name (String.concat "; " found);
      exit 1 )
  in
  let next = mk_call (v "next") [] in
  stale "read after the local is assigned"
    [match_ "t" ["a0"] [Bind_variable (id "t", Existing, next); Return (Some (v "a0"))]]
    ["a0@t"];
  stale "read before it is not"
    [match_ "t" ["a0"] [decl "x" (v "a0"); Bind_variable (id "t", Existing, next); Return (Some (v "x"))]]
    [];
  stale "nor read through a pointer given a new value"
    [ Bind_variable (id "t", Declare (Pointer tree, None), Unary (Address_of, v "u"));
      match_ "t" ["a0"] [Bind_variable (id "t", Existing, next); Return (Some (v "a0"))] ]
    [];
  stale "nor bound again after it"
    [ match_ "t" ["a0"] [Bind_variable (id "t", Existing, next); match_ "t" ["a0"] [Return (Some (v "a0"))]] ]
    []
