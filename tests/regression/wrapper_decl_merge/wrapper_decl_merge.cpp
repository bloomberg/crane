#include <wrapper_decl_merge.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
WrapperDeclMerge::A::Nat::fa(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
WrapperDeclMerge::B::Nat::fb(const unsigned int n) {
  return (std::move(n) + 1);
}
