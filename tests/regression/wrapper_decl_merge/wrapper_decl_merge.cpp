#include "wrapper_decl_merge.h"

unsigned int WrapperDeclMerge::A::Nat::fa(const unsigned int n) { return n; }

unsigned int WrapperDeclMerge::B::Nat::fb(const unsigned int n) {
  return (n + 1);
}
