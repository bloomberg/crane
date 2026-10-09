#include "loopify_inner_instance_call.h"

/// ITree's Functor_stateT is not recursive: its fmap calls the
/// *inner* functor's fmap.  With Set Crane Loopify it is nevertheless
/// loopified, as if that inner call were a self-call: the static method
/// Monads::Functor_stateT<...>::fmap gets a one-frame _Enter stack
/// starting with const Functor_stateT<_tcI0, T1> *_self = this;, and
/// this in a static member function does not compile ("invalid use of
/// 'this' outside of a non-static member function").  Monad_stateT's
/// bind gets the same treatment.
///
/// Found in Vellvm with the global Set Crane Loopify (3 of its 59
/// errors).  Even where it compiled, a call to another instance's method
/// treated as recursion would be a wrong program, not just a slow one.
Itree<LoopifyInnerInstanceCall::Ev, std::pair<uint64_t, uint64_t>>
LoopifyInnerInstanceCall::bumped(std::monostate) {
  static const auto fmap = crane::immortal(
      Monads::template Functor_stateT<
          Functor_itree<LoopifyInnerInstanceCall::Ev>, uint64_t>::
          template fmap<uint64_t, uint64_t>(
              [](uint64_t x) { return (x + UINT64_C(1)); }, st));
  return crane_any_cast<
      Itree<LoopifyInnerInstanceCall::Ev, std::pair<uint64_t, uint64_t>>>(
      fmap(UINT64_C(5)));
}

/// 5 is the state, 41 + 1 the value.
Itree<LoopifyInnerInstanceCall::Ev, bool>
LoopifyInnerInstanceCall::check(std::monostate) {
  return Monad_itree<LoopifyInnerInstanceCall::Ev>::template bind<
      std::pair<uint64_t, uint64_t>, bool>(
      bumped(std::monostate{}), [](const std::pair<uint64_t, uint64_t> &p) {
        return Monad_itree<LoopifyInnerInstanceCall::Ev>::template ret<bool>(
            (p.first == UINT64_C(5) && p.second == UINT64_C(42)));
      });
}
