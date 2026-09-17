#include <hk_class_arg_numbering.h>

#include <cassert>

int main() {
  // one step of (fun m => Some (S m)) on 3 gives Some 4.
  auto r = HkClassArgNumbering::use(Nat::s(Nat::s(Nat::s(Nat::o()))));
  assert(r.has_value());
  return 0;
}
