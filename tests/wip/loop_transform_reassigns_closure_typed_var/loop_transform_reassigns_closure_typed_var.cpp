#include "loop_transform_reassigns_closure_typed_var.h"

/// Takes a unit so that Crane leaves it a free function and something
/// concrete instantiates map_In.
Lst<Nat> run(std::monostate) {
  return Lst<Nat>::cons(
             Nat::s(Nat::o()),
             Lst<Nat>::cons(Nat::s(Nat::s(Nat::o())), Lst<Nat>::nil()))
      .go(Nat::s(Nat::s(Nat::s(Nat::o()))));
}
