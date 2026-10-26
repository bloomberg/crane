(* The moved-value validator on reuse arms: a token is consumed once, and
   nothing reads its local after; what was taken out of the local before
   is not read of it. *)

open Names
open Crane_plugin
open Minicpp

let id = Id.of_string
let v x = CPPvar (id x)
let tree = Tglob (GlobRef.VarRef (id "tree"), [], [])

(* [tree::node_crane_reuse(args)], the token first. *)
let reuse args = mk_call (CPPqualified_t (tree, Generated_name.companion (id "node") "reuse")) args

(* [std::get<tree::Node>(t.v_mut()).f], a field of the alternative [t] holds. *)
let field t f =
  CPPaccess (Adot, CPPstd_get (Tqualified (tree, id "Node"), Some (mk_call (CPPaccess (Adot, v t, id "v_mut")) [])), id f)

(* [std::get<tree::Node>(t.v_mut())], the alternative [t] holds. *)
let alternative t = CPPstd_get (Tqualified (tree, id "Node"), Some (mk_call (CPPaccess (Adot, v t, id "v_mut")) []))

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
  let found = List.map Id.to_string (Move_check.moved_reads body) in
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
    []
