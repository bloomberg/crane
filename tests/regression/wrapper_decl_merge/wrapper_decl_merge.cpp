#include <wrapper_decl_merge.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
WrapperDeclMerge::A::Nat::fa(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
WrapperDeclMerge::B::Nat::fb(unsigned int n) {
  return (n + 1);
}
