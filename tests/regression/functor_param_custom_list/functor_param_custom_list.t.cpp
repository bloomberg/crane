#include <functor_param_custom_list.h>
#include <cassert>
#include <deque>
#include <iostream>

using M = FunctorParamCustomList;

int main() {
  assert(M::all_digits(std::deque<uint64_t>{}));
  assert(M::all_digits(std::deque<uint64_t>{1, 2, 9}));
  assert(!M::all_digits(std::deque<uint64_t>{1, 20, 3}));
  std::cout << "all_digits [1; 2; 9] = " << M::all_digits(std::deque<uint64_t>{1, 2, 9}) << " (want 1)" << std::endl;
  return 0;
}
