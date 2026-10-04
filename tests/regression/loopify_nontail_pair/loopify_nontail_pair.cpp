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
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
  };

  /// CraneCont_x: saves [x], resumes after recursive call, then processes rest.
  struct CraneCont_x {
    uint64_t x;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_x>;
  std::pair<std::pair<uint64_t, List<uint64_t>>, List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{l});
  /// Loopified countdown: CraneEnter -> CraneCont_x.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = std::move(_f.l);
      auto [_x, o] = classify(l);
      if (o.has_value()) {
        const std::pair<uint64_t, List<uint64_t>> &p = *o;
        const auto &[x, xs] = p;
        _stack.emplace_back(CraneCont_x{x});
        _stack.emplace_back(CraneEnter{xs});
      } else {
        _result = std::make_pair(
            std::make_pair(UINT64_C(0), List<uint64_t>::nil()), l);
      }
    } else {
      auto _f = std::move(std::get<CraneCont_x>(_frame));
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
