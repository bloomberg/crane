#include <typed_fit_case_argument.h>

#include <cassert>
#include <iostream>

int main() {
  using T = TypedFitCaseArgument;
  assert(T::via_method(true) == 1);
  assert(T::via_method(false) == 2);
  assert(T::via_local_fix(0) == 0);
  assert(T::via_local_fix(1) == 0);
  assert(T::via_record_len(List<bool>::nil()) == 0);
  assert(T::via_record_len(List<bool>::cons(true, List<bool>::nil())) == 1);
  assert(T::via_eta == 3);
  assert(T::plain(true) == 1);
  std::cout << "ok" << std::endl;
  return 0;
}
