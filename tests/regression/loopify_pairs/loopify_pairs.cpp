#include "loopify_pairs.h"

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>
LoopifyPairs::unzip(
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l) {
  if (std::holds_alternative<
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
          l.v())) {
    return std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<
        typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
        l.v());
    const auto &[x, y] = a0;
    auto [xs, ys] = unzip(*a1);
    return std::make_pair(list<uint64_t>::cons(x, std::move(xs)),
                          list<uint64_t>::cons(y, std::move(ys)));
  }
}

/// partition3 pivot l three-way partition around pivot.
std::pair<LoopifyPairs::list<uint64_t>,
          std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>>
LoopifyPairs::partition3(uint64_t pivot,
                         const LoopifyPairs::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(
        list<uint64_t>::nil(),
        std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
    auto [lt, p] = partition3(pivot, *a1);
    auto [eq, gt] = std::move(p);
    if (a0 < pivot) {
      return std::make_pair(list<uint64_t>::cons(a0, std::move(lt)),
                            std::make_pair(std::move(eq), std::move(gt)));
    } else {
      if (a0 == pivot) {
        return std::make_pair(
            std::move(lt),
            std::make_pair(list<uint64_t>::cons(a0, std::move(eq)),
                           std::move(gt)));
      } else {
        return std::make_pair(
            std::move(lt),
            std::make_pair(std::move(eq),
                           list<uint64_t>::cons(a0, std::move(gt))));
      }
    }
  }
}

/// min_max l finds both min and max in one pass.
std::pair<uint64_t, uint64_t>
LoopifyPairs::min_max(const LoopifyPairs::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
    auto &&_sv = *a1;
    if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
            _sv.v())) {
      return std::make_pair(a0, a0);
    } else {
      auto [mn, mx] = min_max(*a1);
      return std::make_pair((a0 <= mn ? a0 : mn), (mx <= a0 ? a0 : mx));
    }
  }
}

/// sum_and_count computes both in one pass.
std::pair<uint64_t, uint64_t>
LoopifyPairs::sum_and_count(const LoopifyPairs::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
    auto [s, c] = sum_and_count(*a1);
    return std::make_pair((a0 + s), (c + 1));
  }
}

/// sum_prod_count triple accumulator.
std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
LoopifyPairs::sum_prod_count(const LoopifyPairs::list<uint64_t> &l) {
  if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
          l.v())) {
    return std::make_pair(UINT64_C(0),
                          std::make_pair(UINT64_C(1), UINT64_C(0)));
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
    auto [s, p0] = sum_prod_count(*a1);
    auto [p, c] = std::move(p0);
    return std::make_pair((a0 + s), std::make_pair((a0 * p), (c + 1)));
  }
}

/// lookup_all key l finds all values associated with key.
LoopifyPairs::list<uint64_t> LoopifyPairs::lookup_all(
    uint64_t key,
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume1: saves [v], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t v;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyPairs::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified lookup_all: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const auto &[k, v] = a0;
        if (k == key) {
          _stack.emplace_back(_Resume1{v});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = list<uint64_t>::cons(_f.v, std::move(_result));
    }
  }
  return _result;
}

/// swap_pairs l swaps elements in each pair.
LoopifyPairs::list<std::pair<uint64_t, uint64_t>> LoopifyPairs::swap_pairs(
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume_a: saves [_s0], resumes after recursive call with _result.
  struct _Resume_a {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_a>;
  LoopifyPairs::list<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified swap_pairs: _Enter -> _Resume_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = list<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const auto &[a, b] = a0;
        _stack.emplace_back(_Resume_a{std::make_pair(b, a)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_a>(_frame));
      _result =
          list<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}
