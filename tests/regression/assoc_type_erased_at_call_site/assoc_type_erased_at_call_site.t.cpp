#include <assoc_type_erased_at_call_site.h>
#include <cassert>
#include <variant>

int main() {
  // The call site is inside [go]; running it is what checks that the caller
  // and the callee agreed on how to spell the parameter type.  [tag_of]
  // returns [fst b] and [b] is [null = (zero_iptr, nil_prov)], so the answer
  // is [O] -- the [S] this asserted before is from the earlier version of the
  // test, whose body returned [ptr_tag].
  assert(std::holds_alternative<typename Nat::O>(AssocTypeErasedAtCallSite::go(Nat::o()).v()));
  return 0;
}
