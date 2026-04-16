#include <deep_destruct.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Tail-recursive list builder — should compile to a loop.
std::shared_ptr<DeepDestruct::mylist<unsigned int>> DeepDestruct::build_aux(
    const unsigned int n,
    std::shared_ptr<DeepDestruct::mylist<unsigned int>> acc) {
  std::shared_ptr<DeepDestruct::mylist<unsigned int>> _result;
  std::shared_ptr<DeepDestruct::mylist<unsigned int>> _loop_acc =
      std::move(acc);
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_acc);
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::shared_ptr<DeepDestruct::mylist<unsigned int>> _next_acc =
          mylist<unsigned int>::mycons(_loop_n, _loop_acc);
      unsigned int _next_n = n_;
      _loop_acc = std::move(_next_acc);
      _loop_n = std::move(_next_n);
    }
  }
  return _result;
}

std::shared_ptr<DeepDestruct::mylist<unsigned int>>
DeepDestruct::build(const unsigned int n) {
  return build_aux(n, mylist<unsigned int>::mynil());
}

/// Simple accessor to observe the result.
__attribute__((pure)) unsigned int DeepDestruct::head_or_zero(
    const std::shared_ptr<DeepDestruct::mylist<unsigned int>> &l) {
  if (std::holds_alternative<
          typename DeepDestruct::mylist<unsigned int>::Mynil>(l->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename DeepDestruct::mylist<unsigned int>::Mycons>(l->v());
    return d_a0;
  }
}
