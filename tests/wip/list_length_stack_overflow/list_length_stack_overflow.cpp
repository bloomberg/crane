#include "list_length_stack_overflow.h"

/// A tail-recursive builder, loopified below, so that constructing the
/// list itself is stack-safe: only the generated List method under test
/// can overflow.
List<uint64_t> ListLengthStackOverflow::bld(uint64_t n, List<uint64_t> acc) {
  List<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t j = _loop_n - 1;
      _loop_acc = List<uint64_t>::cons(j, std::move(_loop_acc));
      _loop_n = j;
    }
  }
}

uint64_t ListLengthStackOverflow::run(uint64_t k) {
  return bld((k + UINT64_C(200000)), List<uint64_t>::nil()).length();
}
