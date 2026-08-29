#include "mem_safety_probe20.h"

MemSafetyProbe20::wrapped MemSafetyProbe20::wrap_if(MemSafetyProbe20::tree t,
                                                    bool b) {
  if (b) {
    return wrapped::wrap(
        [=](uint64_t n) mutable { return (t.tree_sum() + n); });
  } else {
    return wrapped::wrap([](uint64_t n) { return n; });
  }
}

MemSafetyProbe20::wrapped
MemSafetyProbe20::wrap_match(MemSafetyProbe20::tree t,
                             MemSafetyProbe20::Choice c) {
  switch (c) {
  case Choice::CLEFT: {
    return wrapped::wrap(
        [=](uint64_t n) mutable { return (t.tree_sum() + n); });
  }
  case Choice::CRIGHT: {
    return wrapped::wrap([](uint64_t n) { return n; });
  }
  default:
    std::unreachable();
  }
}

std::pair<MemSafetyProbe20::wrapped, uint64_t>
MemSafetyProbe20::pair_from_if(MemSafetyProbe20::tree t, bool b) {
  if (b) {
    return std::make_pair(
        wrapped::wrap([=](uint64_t n) mutable { return (t.tree_sum() + n); }),
        t.tree_sum());
  } else {
    return std::make_pair(wrapped::wrap([](uint64_t n) { return n; }),
                          UINT64_C(0));
  }
}

MemSafetyProbe20::wrapped MemSafetyProbe20::wrap_local(uint64_t n, bool b) {
  MemSafetyProbe20::tree t = tree::node(tree::leaf(), n, tree::leaf());
  if (b) {
    return wrapped::wrap(
        [=](uint64_t m) mutable { return (t.tree_sum() + m); });
  } else {
    return wrapped::wrap([](uint64_t m) { return m; });
  }
}

MemSafetyProbe20::wrapped
MemSafetyProbe20::nested_wrap(MemSafetyProbe20::tree t, bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return wrapped::wrap(
          [=](uint64_t n) mutable { return (t.tree_sum() + n); });
    } else {
      return wrapped::wrap([=](uint64_t n) mutable {
        return ((t.tree_sum() * UINT64_C(2)) + n);
      });
    }
  } else {
    return wrapped::wrap([](uint64_t n) { return n; });
  }
}

MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped>
MemSafetyProbe20::wrap_list(MemSafetyProbe20::tree t, bool b) {
  if (b) {
    return mylist<MemSafetyProbe20::wrapped>::mycons(
        wrapped::wrap([=](uint64_t n) mutable { return (t.tree_sum() + n); }),
        mylist<MemSafetyProbe20::wrapped>::mycons(
            wrapped::wrap([=](uint64_t n) mutable {
              return ((t.tree_sum() + t.tree_sum()) + n);
            }),
            mylist<MemSafetyProbe20::wrapped>::mynil()));
  } else {
    return mylist<MemSafetyProbe20::wrapped>::mycons(
        wrapped::wrap([](uint64_t n) { return n; }),
        mylist<MemSafetyProbe20::wrapped>::mynil());
  }
}

uint64_t MemSafetyProbe20::sum_wrapped(
    const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> &l,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::decay_t<decltype(std::declval<MemSafetyProbe20::wrapped &>().unwrap(
        std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_wrapped: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe20::mylist<MemSafetyProbe20::wrapped> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe20::mylist<
              MemSafetyProbe20::wrapped>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe20::mylist<
            MemSafetyProbe20::wrapped>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0.unwrap(x)});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}
