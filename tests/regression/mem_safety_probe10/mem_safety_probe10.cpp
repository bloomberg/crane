#include <mem_safety_probe10.h>

unsigned int MemSafetyProbe10::sum_fns(
    const MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>
        *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>
          &l = *(_f.l);
      if (std::holds_alternative<typename MemSafetyProbe10::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe10::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0(0u)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// TEST 3: Recursive function returning a list of closures.
/// Each closure captures the tree node's value and subtrees.
MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe10::collect_adders(const MemSafetyProbe10::tree &t) {
  std::unique_ptr<
      MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
            _loop_t.v())) {
      *(_write) = std::make_unique<
          MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
      MemSafetyProbe10::tree d_a0_value = *(d_a0);
      MemSafetyProbe10::tree d_a2_value = *(d_a2);
      auto _cell = std::make_unique<
          MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](const unsigned int n) mutable { return (d_a1 + n); },
              nullptr));
      auto _cell1 = std::make_unique<
          MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](const unsigned int n) mutable {
                return (d_a0_value.tree_sum() + n);
              },
              nullptr));
      auto _cell2 = std::make_unique<
          MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](const unsigned int n) mutable {
                return (d_a2_value.tree_sum() + n);
              },
              nullptr));
      std::get<
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons>(
          _cell1->v_mut())
          .d_a1 = std::move(_cell2);
      std::get<
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons>(
          _cell->v_mut())
          .d_a1 = std::move(_cell1);
      *(_write) = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    std::get<typename mylist<
                        std::function<unsigned int(unsigned int)>>::Mycons>(
                        std::get<typename mylist<
                            std::function<unsigned int(unsigned int)>>::Mycons>(
                            (*_write)->v_mut())
                            .d_a1->v_mut())
                        .d_a1->v_mut())
                    .d_a1;
      _loop_t = d_a0_value;
      continue;
    }
  }
  return std::move(*(_head));
}

/// TEST 4: Closure returned from nested match.
/// Tests return_captures_by_value through Sif branches.
unsigned int MemSafetyProbe10::choose_fn(const std::optional<bool> &o,
                                         const unsigned int v,
                                         const unsigned int n) {
  if (o.has_value()) {
    const bool &b = *o;
    if (b) {
      return (v + n);
    } else {
      return (v * n);
    }
  } else {
    return n;
  }
}

/// TEST 6: Function returning closure in pair.
/// Tests pair construction with closure.
std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
MemSafetyProbe10::pair_with_fn(const unsigned int n) {
  return std::make_pair([=](const unsigned int x) mutable { return (n + x); },
                        (n * 2u));
}

/// TEST 7: Mutually recursive functions using a fixpoint
/// where one captures the other's result as a closure.
MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe10::build_tree_fns(const MemSafetyProbe10::tree &t,
                                 const unsigned int depth) {
  std::unique_ptr<
      MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  unsigned int _loop_depth = depth;
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (_loop_depth <= 0) {
      *(_write) = std::make_unique<
          MemSafetyProbe10::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      unsigned int d = _loop_depth - 1;
      if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
              _loop_t.v())) {
        *(_write) = std::make_unique<MemSafetyProbe10::mylist<
            std::function<unsigned int(unsigned int)>>>(
            mylist<std::function<unsigned int(unsigned int)>>::mycons(
                [](const unsigned int n) { return n; },
                mylist<std::function<unsigned int(unsigned int)>>::mynil()));
        break;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
        MemSafetyProbe10::tree d_a0_value = *(d_a0);
        MemSafetyProbe10::tree d_a2_value = *(d_a2);
        auto _cell = std::make_unique<MemSafetyProbe10::mylist<
            std::function<unsigned int(unsigned int)>>>(
            typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
                [=](const unsigned int n) mutable { return (d_a1 + n); },
                nullptr));
        auto _cell1 = std::make_unique<MemSafetyProbe10::mylist<
            std::function<unsigned int(unsigned int)>>>(
            typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
                [=](const unsigned int n) mutable {
                  return ((d_a0_value.tree_sum() + d_a2_value.tree_sum()) + n);
                },
                nullptr));
        std::get<
            typename mylist<std::function<unsigned int(unsigned int)>>::Mycons>(
            _cell->v_mut())
            .d_a1 = std::move(_cell1);
        *(_write) = std::move(_cell);
        _write = &std::get<typename mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(
                      std::get<typename mylist<
                          std::function<unsigned int(unsigned int)>>::Mycons>(
                          (*_write)->v_mut())
                          .d_a1->v_mut())
                      .d_a1;
        _loop_depth = d;
        _loop_t = d_a0_value;
        continue;
      }
    }
  }
  return std::move(*(_head));
}
