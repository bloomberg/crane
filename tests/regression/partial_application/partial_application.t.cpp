#include <partial_application.h>

#include <cassert>
#include <variant>

int main() {
  // Mapping (= 0) over the pair (0, mk 1 0) should give (true, mk 1 true).
  auto r = PartialApplication::convert({Nat::o(), Box<Nat>::mk(Nat::s(Nat::o()), Nat::o())});
  assert(r.first == true);
  return 0;
}
