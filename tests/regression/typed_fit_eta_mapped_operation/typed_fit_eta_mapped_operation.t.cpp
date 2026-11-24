#include <typed_fit_eta_mapped_operation.h>

#include <cassert>
#include <iostream>

int main() {
  using T = TypedFitEtaMappedOperation;
  assert(T::use(List<uint64_t>::nil(), true) == 0);
  assert(T::use(List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil())), false) == 0);
  std::cout << "ok" << std::endl;
  return 0;
}
