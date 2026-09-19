#include "functor_record_proj_as_static.h"

#include <cassert>
#include <variant>

int main() {
  // The empty map projects to an empty tree, so its size is zero.
  auto m = IM::empty<Nat>();
  assert(std::holds_alternative<typename Nat::O>(Qp::use(m).v()));
  return 0;
}
