#include "loopify_nontail_pair.h"

std::pair<uint64_t, std::optional<std::pair<uint64_t, List<uint64_t>>>>
LoopifyNontailPair::classify(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::make_pair(UINT64_C(0),
                          std::optional<std::pair<uint64_t, List<uint64_t>>>());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return std::make_pair(
        a0, std::make_optional<std::pair<uint64_t, List<uint64_t>>>(
                std::make_pair(a0, *a1)));
  }
}

std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>>
LoopifyNontailPair::countdown(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of countdown: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> l;
  };

  struct _after_countdown_in_pair {
    uint64_t x;
  };

  using _frame = std::variant<_call, _after_countdown_in_pair>;
  std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = _f.l;
      auto [_x, o] = classify(l);
      if (o.has_value()) {
        const std::pair<uint64_t, List<uint64_t>> &p = *o;
        const auto &[x, xs] = p;
        _stack.emplace_back(_after_countdown_in_pair{x});
        _stack.emplace_back(_call{xs});
      } else {
        _result = std::make_pair(
            std::make_pair(UINT64_C(0), List<uint64_t>::nil()), l);
      }
    } else {
      auto _f = std::move(std::get<_after_countdown_in_pair>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      auto [p0, rest] = std::move(_result);
      auto [cnt, acc] = std::move(p0);
      _result = std::make_pair(
          std::make_pair((cnt + 1), List<uint64_t>::cons(x, std::move(acc))),
          std::move(rest));
    }
  }
  return _result;
}

std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>>
LoopifyNontailPair::countdown_top(const List<uint64_t> &x0_) {
  return countdown(x0_);
}

uint64_t LoopifyNontailPair::run_count(const List<uint64_t> &l) {
  return (countdown_top(l).first).first;
}
