(* The moved-value validator on reuse arms: a token is consumed once, and
   nothing reads its local after; what was taken out of the local before
   is not read of it. *)

open Names
open Crane_plugin
open Minicpp

let id = Id.of_string

(* The checks read CppIR; the bodies are built in MiniCpp and lowered. *)
let lower = List.map Legacy_minicpp_to_cpp_ir.lower_stmt
let lower_params = List.map (fun (x, t) -> (x, Legacy_minicpp_to_cpp_ir.lower_type t))
let v x = CPPvar (id x)
let tree = Tglob (GlobRef.VarRef (id "tree"), [], [])

(* [tree::node_crane_reuse(args)], the token first. *)
let reuse args = mk_call (CPPqualified_t (tree, Generated_name.companion (id "node") "reuse")) args

(* [std::get<tree::Node>(t.v_mut()).f], a field of the alternative [t] holds. *)
let field t f =
  CPPaccess (Adot, CPPstd_get (Tqualified (tree, id "Node"), Some (mk_call (CPPaccess (Adot, v t, id "v_mut")) [])), id f)

(* [std::get<tree::Node>(t.v_mut())], the alternative [t] holds. *)
let alternative t = CPPstd_get (Tqualified (tree, id "Node"), Some (mk_call (CPPaccess (Adot, v t, id "v_mut")) []))

(* [%a0.first] applied to [pair], instantiated ({!Minicpp.foreign}). *)
let projection f pair =
  CPPforeign
    ( Foreign_call,
      { fr_custom = GlobRef.VarRef (id f);
        fr_types = [];
        fr_values = [pair];
        fr_yields = None;
        fr_pieces = [Fp_value 0; Fp_text ("." ^ f)] } )

(* A frame pushed onto a stack, as a loop saving its continuation does. *)
let push args = mk_call (CPPaccess (Adot, v "_stack", id "push_back")) [CPPbraced args]

(* A match on [t] whose one branch binds [fields] into it. *)
let match_ t fields body =
  let binding x = {fb_name = id x; fb_type = Tauto; fb_used = true; fb_binder = None} in
  Smatch
    ( {sc_expr = mk_call (CPPaccess (Adot, v t, id "v_mut")) []; sc_access = Adot; sc_owned = true; sc_flat = false},
      [ { smb_ctor_type = Tqualified (tree, id "Node");
          smb_var = None;
          smb_field_bindings = List.map binding fields;
          smb_extra_conds = [];
          smb_body = body } ],
      None )

let check name body expected =
  let found = List.map Id.to_string (Move_check.moved_reads (lower body)) in
  if found <> expected then (
    Printf.eprintf "move_check: %s: found [%s]\n" name (String.concat "; " found);
    exit 1 )

let decl x e = Sasgn (id x, Declare (Tauto, None), e)

let () =
  check "fields taken out, then the storage"
    [ decl "l" (CPPmove (CPPderef (field "t" "a0")));
      decl "k" (CPPmove (field "t" "a1"));
      Sreturn (Some (reuse [CPPmove (v "t"); CPPmove (v "l"); v "k"])) ]
    [];
  check "the token consumed twice"
    [ Sexpr (reuse [CPPmove (v "t"); v "k"]);
      Sreturn (Some (reuse [CPPmove (v "t"); v "k"])) ]
    ["t"];
  check "the local read after its storage is rebuilt"
    [ decl "n" (reuse [CPPmove (v "t"); v "k"]);
      Sreturn (Some (mk_call (CPPaccess (Adot, v "t", id "v")) [])) ]
    ["t"];
  check "the local read beside its token"
    [Sreturn (Some (reuse [CPPmove (v "t"); mk_call (CPPaccess (Adot, v "t", id "v")) []]))]
    ["t"];
  check "a child cell handed over, then read"
    [ decl "xs" (CPPmove (CPPderef (field "t" "a1")));
      decl "n" (reuse [CPPmove (field "t" "a1"); v "xs"]);
      Sreturn (Some (field "t" "a1")) ]
    ["t"];
  check "a child cell handed over, a sibling field read"
    [ decl "n" (reuse [CPPmove (field "t" "a1"); CPPmove (field "t" "a0")]);
      Sreturn (Some (v "n")) ]
    [];
  check "the local assigned afresh after its storage is rebuilt"
    [ decl "n" (reuse [CPPmove (v "t"); v "k"]);
      Sasgn (id "t", Existing, v "n");
      Sreturn (Some (v "t")) ]
    [];
  check "a field read through a binding after its local is moved"
    [ Sbind ([id "a0"; id "a1"], alternative "t");
      Sexpr (push [CPPmove (v "t")]);
      Sexpr (push [v "a0"]) ]
    ["t"];
  check "a field read through a binding beside a move of its local"
    [Sbind ([id "a0"], alternative "t"); Sexpr (push [CPPmove (v "t"); v "a0"])]
    ["t"];
  check "a local copied, then a field moved out of it, in one initialiser"
    [Sbind ([id "a0"], alternative "t"); Sexpr (push [v "t"; CPPmove (v "a0")])]
    [];
  check "a local moved and a field read in a call's arguments"
    [Sbind ([id "a0"], alternative "t"); Sexpr (mk_call (v "f") [v "t"; CPPmove (v "a0")])]
    ["t"];
  check "a field moved out through a binding, then the storage"
    [ Sbind ([id "a0"; id "a1"], alternative "t");
      decl "l" (CPPmove (v "a0"));
      Sreturn (Some (reuse [CPPmove (v "t"); CPPmove (v "l")])) ]
    [];
  check "a field handed over through a binding beside its storage"
    [Sbind ([id "a0"], alternative "t"); Sreturn (Some (reuse [CPPmove (v "t"); CPPmove (v "a0")]))]
    ["t"];
  check "two bindings into one local, one moved and the other read"
    [Sbind ([id "a0"; id "a1"], alternative "t"); Sexpr (push [CPPmove (v "a0")]); Sreturn (Some (v "a1"))]
    [];
  check "a binding into a computed value"
    [ Sbind ([id "a0"], mk_call (v "f") [v "t"]);
      Sexpr (push [CPPmove (v "t")]);
      Sreturn (Some (v "a0")) ]
    [];
  check "a match's field read after its scrutinee is moved"
    [match_ "t" ["a0"] [Sexpr (push [CPPmove (v "t")]); Sreturn (Some (v "a0"))]]
    ["t"];
  check "a match's field read after a binding of the same name"
    [match_ "t" ["a0"] [Sbind ([id "a0"], mk_call (v "f") []); Sexpr (push [CPPmove (v "t")]); Sreturn (Some (v "a0"))]]
    [];
  check "a reference declared to a field, read after its local is moved"
    [ Sasgn (id "r", Declare (Tref (Lvalue, Tauto), None), field "t" "a0");
      Sexpr (push [CPPmove (v "t")]);
      Sreturn (Some (v "r")) ]
    ["t"];
  check "a copy of a field, read after its local is moved"
    [decl "c" (field "t" "a0"); Sexpr (push [CPPmove (v "t")]); Sreturn (Some (v "c"))]
    [];
  check "each component taken out of a pair through its instantiated projection"
    [Sexpr (push [projection "first" (CPPmove (v "p")); projection "second" (CPPmove (v "p"))])]
    []

(* A callable's parameters and body against the convention its plan
   states: [f] owns [a] and lends [b]. *)
let () =
  let f = GlobRef.VarRef (id "f") in
  Callable_abi.install [Callable_abi.of_head ~passing:[Owned; Borrowed] ~callee:f ~scheme:None []] [];
  let cref = Tref (Lvalue, Tconst tree) in
  let convention name params body expected =
    let found = Option.map List.length (Move_check.convention_violations f (lower_params params) (lower body)) in
    if found <> Some expected then (
      Printf.eprintf "move_check: %s: %s violations, expected %d\n" name
        (match found with Some n -> string_of_int n | None -> "no plan's") expected;
      exit 1 )
  in
  convention "as the plan has them" [(id "a", tree); (id "b", cref)] [Sreturn (Some (mk_call (v "g") [CPPmove (v "a"); v "b"]))] 0;
  convention "an owned parameter declared by reference" [(id "a", cref); (id "b", cref)] [] 1;
  convention "a lent parameter moved out of" [(id "a", tree); (id "b", cref)] [Sreturn (Some (CPPmove (v "b")))] 1;
  convention "a lent parameter's name declared again and moved"
    [(id "a", tree); (id "b", cref)]
    [decl "b" (v "a"); Sreturn (Some (CPPmove (v "b")))]
    0;
  convention "a parameter the plan does not pass" [(id "a", tree)] [] 1;
  if Move_check.convention_violations (GlobRef.VarRef (id "unplanned")) [] [] <> None then (
    prerr_endline "move_check: a callable with no plan has a convention";
    exit 1 )

(* A reference bound into a local is not read after the local is given a
   new value: the storage it names is gone.  A pointer local given a new
   value leaves what it pointed at; a reference bound after the assignment
   names the new value. *)
let () =
  let stale name body expected =
    let found = List.map (fun (a, b) -> Id.to_string a ^ "@" ^ Id.to_string b) (Move_check.stale_references (lower body)) in
    if found <> expected then (
      Printf.eprintf "move_check: %s: stale [%s]\n" name (String.concat "; " found);
      exit 1 )
  in
  let next = mk_call (v "next") [] in
  stale "read after the local is assigned"
    [match_ "t" ["a0"] [Sasgn (id "t", Existing, next); Sreturn (Some (v "a0"))]]
    ["a0@t"];
  stale "read before it is not"
    [match_ "t" ["a0"] [decl "x" (v "a0"); Sasgn (id "t", Existing, next); Sreturn (Some (v "x"))]]
    [];
  stale "nor read through a pointer given a new value"
    [ Sasgn (id "t", Declare (Tptr tree, None), CPPunop (Uaddr, v "u"));
      match_ "t" ["a0"] [Sasgn (id "t", Existing, next); Sreturn (Some (v "a0"))] ]
    [];
  stale "nor bound again after it"
    [ match_ "t" ["a0"] [Sasgn (id "t", Existing, next); match_ "t" ["a0"] [Sreturn (Some (v "a0"))]] ]
    []
