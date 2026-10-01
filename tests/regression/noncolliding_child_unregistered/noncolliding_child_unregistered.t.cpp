#include "noncolliding_child_unregistered.h"
#include <cassert>
#include <cstdio>

int main() {
  // [RawIDOrd] is the bystander: nested correctly inside the wrapper struct,
  // but referenced from outside without the wrapper's name.
  assert(via_non_colliding(Raw_id::name(Nat::o()), Raw_id::name(Nat::o())));
  assert(!via_non_colliding(Raw_id::name(Nat::o()), Raw_id::anon(Nat::o())));

  // The colliding child and the file's own declaration are the controls.
  assert(std::holds_alternative<Nat::S>(
      via_colliding(Nat::s(Nat::o()), Nat::o()).v()));
  assert(via_file(Raw_id::anon(Nat::o()), Raw_id::anon(Nat::o())));

  printf("All noncolliding_child_unregistered tests passed!\n");
  return 0;
}
