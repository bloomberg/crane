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
    []
