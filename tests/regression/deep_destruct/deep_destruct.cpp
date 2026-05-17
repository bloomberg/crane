#include "deep_destruct.h"

/// Tail-recursive list builder — should compile to a loop.
DeepDestruct::mylist<uint64_t>
DeepDestruct::build_aux(uint64_t n, DeepDestruct::mylist<uint64_t> acc) {
  DeepDestruct::mylist<uint64_t> _result;
  DeepDestruct::mylist<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_acc);
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_acc = mylist<uint64_t>::mycons(_loop_n, std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
  return _result;
}

DeepDestruct::mylist<uint64_t> DeepDestruct::build(uint64_t n) {
  return build_aux(n, mylist<uint64_t>::mynil());
}

/// Simple accessor to observe the result.
uint64_t DeepDestruct::head_or_zero(const DeepDestruct::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename DeepDestruct::mylist<uint64_t>::Mynil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepDestruct::mylist<uint64_t>::Mycons>(l.v());
    return a0;
  }
}
