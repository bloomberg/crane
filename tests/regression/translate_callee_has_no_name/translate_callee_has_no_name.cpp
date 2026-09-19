#include "translate_callee_has_no_name.h"

std::shared_ptr<ITree<Nat>> TranslateCalleeHasNoName::use(Nat n) {
  return w<Nat>(itree_ret(std::move(n)));
}
