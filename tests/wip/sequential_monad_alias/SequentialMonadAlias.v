(* A computation in a sequential monad, typed through an alias of it.

   Under the sequential ITree mapping an [itree ioE unit] is no C++ value:
   its declaration is a function run when performed, void-ified --
   [static void direct()] below.  Typed [IOt unit] instead, the same
   computation is read off its spelling, which is no monad, and comes out
   as a value of an alias Crane never declares:

     static inline const IOt<std::monostate> aliased =
         std::cout << std::string("aliased") << '\n';
     static inline const IOt<std::monostate> both = []() {
       aliased;
       return direct();
     }();
     static IOt<std::monostate> twice(const std::monostate &m);

     error: no template named 'IOt'

   and, were it declared, both prints would run during static
   initialisation, once, and [twice] would perform nothing.

   Expected: every declaration below is spelled exactly as [direct] is --
   the alias is the monad.  The reified mode reads its mode through aliases
   (regression state_t_alias_reified); the sequential readings --
   [Translation_support.thunk_reason], void-ification
   ([ml_type_is_void_call]), [convert_ml_type_to_cpp_type]'s erasure of the
   monad, and the alias's own declaration -- all read the spelling
   ([Ml_type_util.is_monadic_ml_type]), so the fix is either each of them
   asking [Ml_type_util.type_monad], or Core expanding an alias of a
   sequential monad, which C++ can never spell, before any of them run. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO.
From ITree Require Import ITree.
From Corelib Require Import PrimString.
Open Scope pstring_scope.

Module SequentialMonadAlias.
  Definition IOt := itree ioE.
  Definition aliased : IOt unit := print_endline "aliased".
  Definition direct : itree ioE unit := print_endline "direct".
  Definition both : IOt unit := ITree.bind aliased (fun _ => direct).
  Definition twice (m : IOt unit) : IOt unit := ITree.bind m (fun _ => m).
End SequentialMonadAlias.

Crane Extraction "sequential_monad_alias" SequentialMonadAlias.
