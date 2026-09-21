#include "dropped_binder_in_instance_method.h"
#include <cassert>
#include <optional>
#include <cstdio>

int main() {
  // [plain] is the control: the identical expression as a plain Definition.
  auto p = plain(std::optional<Nat>(Nat::s(Nat::o())));
  assert(p.has_value());

  // [run] goes through the instance field, which is where the binder is lost.
  auto r = run(std::optional<Nat>(Nat::s(Nat::o())));
  assert(r.has_value());

  printf("All dropped_binder_in_instance_method tests passed!\n");
  return 0;
}
