#include "mem_safety_probe20.h"

/// TEST 1: Return wrapped closure from if-branch.
/// The if becomes top-level Sif. return_captures_by_value sees
/// Sif, matches s -> s, leaves lambda as &.
MemSafetyProbe20::wrapped MemSafetyProbe20::wrap_if(MemSafetyProbe20::tree t,
                                                    const bool b) {
  if (b) {
    return wrapped::wrap(
        [=](const unsigned int n) mutable { return (t.tree_sum() + n); });
  } else {
    return wrapped::wrap([](const unsigned int n) { return n; });
  }
}

MemSafetyProbe20::wrapped
MemSafetyProbe20::wrap_match(MemSafetyProbe20::tree t,
                             const MemSafetyProbe20::Choice c) {
  switch (c) {
  case Choice::e_CLEFT: {
    return wrapped::wrap(
        [=](const unsigned int n) mutable { return (t.tree_sum() + n); });
  }
  case Choice::e_CRIGHT: {
    return wrapped::wrap([](const unsigned int n) { return n; });
  }
  default:
    std::unreachable();
  }
}

/// TEST 3: Pair of closure and value, returned from if.
/// Uses prod to wrap the closure.
std::pair<MemSafetyProbe20::wrapped, unsigned int>
MemSafetyProbe20::pair_from_if(MemSafetyProbe20::tree t, const bool b) {
  if (b) {
    return std::make_pair(wrapped::wrap([=](const unsigned int n) mutable {
                            return (t.tree_sum() + n);
                          }),
                          t.tree_sum());
  } else {
    return std::make_pair(wrapped::wrap([](const unsigned int n) { return n; }),
                          0u);
  }
}

/// TEST 4: Wrapped closure captured in a locally-constructed tree.
/// The let-bound tree is stack-allocated.
MemSafetyProbe20::wrapped MemSafetyProbe20::wrap_local(const unsigned int n,
                                                       const bool b) {
  MemSafetyProbe20::tree t = tree::node(tree::leaf(), n, tree::leaf());
  if (b) {
    return wrapped::wrap(
        [=](const unsigned int m) mutable { return (t.tree_sum() + m); });
  } else {
    return wrapped::wrap([](const unsigned int m) { return m; });
  }
}

/// TEST 6: Nested wrapped closure: wrapped inside a pair inside if.
MemSafetyProbe20::wrapped
MemSafetyProbe20::nested_wrap(MemSafetyProbe20::tree t, const bool b1,
                              const bool b2) {
  if (b1) {
    if (b2) {
      return wrapped::wrap(
          [=](const unsigned int n) mutable { return (t.tree_sum() + n); });
    } else {
      return wrapped::wrap([=](const unsigned int n) mutable {
        return ((t.tree_sum() * 2u) + n);
      });
    }
  } else {
    return wrapped::wrap([](const unsigned int n) { return n; });
  }
}

MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped>
MemSafetyProbe20::wrap_list(MemSafetyProbe20::tree t, const bool b) {
  if (b) {
    return mylist<MemSafetyProbe20::wrapped>::mycons(
        wrapped::wrap(
            [=](const unsigned int n) mutable { return (t.tree_sum() + n); }),
        mylist<MemSafetyProbe20::wrapped>::mycons(
            wrapped::wrap([=](const unsigned int n) mutable {
              return ((t.tree_sum() + t.tree_sum()) + n);
            }),
            mylist<MemSafetyProbe20::wrapped>::mynil()));
  } else {
    return mylist<MemSafetyProbe20::wrapped>::mycons(
        wrapped::wrap([](const unsigned int n) { return n; }),
        mylist<MemSafetyProbe20::wrapped>::mynil());
  }
}

unsigned int MemSafetyProbe20::sum_wrapped(
    const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> &l,
    const unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    decltype(std::declval<MemSafetyProbe20::wrapped &>().unwrap(
        std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(&l));
  /// Loopified sum_wrapped: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> &l = *(_f.l);
      if (std::holds_alternative<typename MemSafetyProbe20::mylist<
              MemSafetyProbe20::wrapped>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe20::mylist<
            MemSafetyProbe20::wrapped>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons(d_a0.unwrap(x)));
        _stack.emplace_back(_Enter(d_a1.get()));
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
