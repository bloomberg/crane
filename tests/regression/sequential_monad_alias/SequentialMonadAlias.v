(* A computation in a sequential monad, typed through an alias of it.

   Under the sequential ITree mapping an [itree ioE unit] is no C++ value:
   its declaration is a function run when performed, void-ified --
   [static void direct()] below.  Typed [IOt unit] instead, the same
   computation was read off its spelling, which is no monad, and came out
   as a value of an alias Crane never declares:

     static inline const IOt<std::monostate> aliased =
         std::cout << std::string("aliased") << '\n';

   which does not compile, and would print once, during static
   initialisation, were [IOt] declared.  An alias of a sequential monad has
   no C++ spelling of its own, so extraction unfolds it to the monad
   ([Extraction.sequential_monad_alias]) and every declaration below is
   spelled as [direct] is: [static void aliased()], [static void both()]. *)
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
