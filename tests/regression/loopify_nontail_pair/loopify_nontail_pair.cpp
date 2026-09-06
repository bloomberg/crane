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
LoopifyNontailPair::countdown(
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
  };

  /// _Cont_x: saves [x], resumes after recursive call, then processes rest.
  struct _Cont_x {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Cont_x>;
  std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(l)});
  /// Loopified countdown: _Enter -> _Cont_x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      auto [_x, o] = classify(l);
      if (o.has_value()) {
        const std::pair<uint64_t, List<uint64_t>> &p = *o;
        const auto &[x, xs] = p;
        _stack.emplace_back(_Cont_x{x});
        _stack.emplace_back(_Enter{xs});
      } else {
        _result = std::make_pair(
            std::make_pair(UINT64_C(0), List<uint64_t>::nil()), std::move(l));
      }
    } else {
      auto _f = std::move(std::get<_Cont_x>(_frame));
      uint64_t x = _f.x;
      std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>> _rc1 =
          std::move(_result);
      auto [p0, rest] = _rc1;
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
