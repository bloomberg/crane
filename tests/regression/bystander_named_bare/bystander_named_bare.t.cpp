#include "bystander_named_bare.h"
#include <cassert>
#include <cstdio>

int main() {
  // The bystander named bare: [start]'s type is spelled through the functor
  // instantiated at [AstLib::RawIDOrd].
  using Tbl = List<std::pair<Raw_id, bool>>;
  assert(std::holds_alternative<Tbl::Nil>(start.v()));

  // The controls: the same bystander named through [::], and the colliding
  // child that the wrapper flattens.
  assert(viaQualified(Raw_id::name(Nat::o()), Raw_id::name(Nat::o())));
  assert(!viaQualified(Raw_id::name(Nat::o()), Raw_id::anon(Nat::o())));
  assert(std::holds_alternative<Nat::S>(
      viaColliding(Nat::s(Nat::o()), Nat::o()).v()));

  printf("All bystander_named_bare tests passed!\n");
  return 0;
}
