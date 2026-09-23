#include <assoc_type_erased_at_call_site.h>
#include <cassert>
#include <variant>

int main() {
  // The call site is inside [go]; running it is what checks that the caller
  // and the callee agreed on how to spell the parameter type.
  assert(std::holds_alternative<typename Nat::S>(AssocTypeErasedAtCallSite::go(Nat::o()).v()));
  return 0;
}
