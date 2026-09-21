#include "method_body_names_later_struct.h"
#include <cassert>
#include <cstdio>

int main() {
  assert(le(Zed::zp(Nat::o()), Zed::zp(Nat::s(Nat::o()))));
  assert(!le(Zed::zp(Nat::s(Nat::o())), Zed::zp(Nat::o())));
  assert(std::holds_alternative<Zed::Zp>(round(Zed::zp(Nat::o())).v()));
  printf("All method_body_names_later_struct tests passed!\n");
  return 0;
}
