#include "mem_safety_probe10.h"

uint64_t MemSafetyProbe10::sum_fns(
    const MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe10::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe10::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0(UINT64_C(0))});
        _stack.emplace_back(_Enter{a1.get()});
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
MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe10::collect_adders(const MemSafetyProbe10::tree &t) {
  std::unique_ptr<MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>
      _head{};
  std::unique_ptr<MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>
      *_write = &_head;
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
            _loop_t.v())) {
      *_write = std::make_unique<
          MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
          mylist<std::function<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
      const MemSafetyProbe10::tree &a0_value = *a0;
      const MemSafetyProbe10::tree &a2_value = *a2;
      auto _cell = std::make_unique<
          MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
          typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) mutable { return (a1 + n); }, nullptr));
      auto _cell1 = std::make_unique<
          MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
          typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) mutable { return (a0_value.tree_sum() + n); },
              nullptr));
      auto _cell2 = std::make_unique<
          MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
          typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) mutable { return (a2_value.tree_sum() + n); },
              nullptr));
      std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
          _cell1->v_mut())
          .a1 = std::move(_cell2);
      std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
          _cell->v_mut())
          .a1 = std::move(_cell1);
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
               std::get<
                   typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
                   std::get<typename mylist<
                       std::function<uint64_t(uint64_t)>>::Mycons>(
                       (*_write)->v_mut())
                       .a1->v_mut())
                   .a1->v_mut())
               .a1;
      _loop_t = a0_value;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 4: Closure returned from nested match.
/// Tests return_captures_by_value through Sif branches.
uint64_t MemSafetyProbe10::choose_fn(const std::optional<bool> &o, uint64_t v,
                                     uint64_t n) {
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
std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
MemSafetyProbe10::pair_with_fn(uint64_t n) {
  return std::make_pair([=](uint64_t x) mutable { return (n + x); },
                        (n * UINT64_C(2)));
}

/// TEST 7: Mutually recursive functions using a fixpoint
/// where one captures the other's result as a closure.
MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe10::build_tree_fns(const MemSafetyProbe10::tree &t,
                                 uint64_t depth) {
  std::unique_ptr<MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>
      _head{};
  std::unique_ptr<MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>
      *_write = &_head;
  uint64_t _loop_depth = std::move(depth);
  MemSafetyProbe10::tree _loop_t = t;
  while (true) {
    if (_loop_depth <= 0) {
      *_write = std::make_unique<
          MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
          mylist<std::function<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      uint64_t d = _loop_depth - 1;
      if (std::holds_alternative<typename MemSafetyProbe10::tree::Leaf>(
              _loop_t.v())) {
        *_write = std::make_unique<
            MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
            mylist<std::function<uint64_t(uint64_t)>>::mycons(
                [](uint64_t n) { return n; },
                mylist<std::function<uint64_t(uint64_t)>>::mynil()));
        break;
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe10::tree::Node>(_loop_t.v());
        const MemSafetyProbe10::tree &a0_value = *a0;
        const MemSafetyProbe10::tree &a2_value = *a2;
        auto _cell = std::make_unique<
            MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
            typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
                [=](uint64_t n) mutable { return (a1 + n); }, nullptr));
        auto _cell1 = std::make_unique<
            MemSafetyProbe10::mylist<std::function<uint64_t(uint64_t)>>>(
            typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
                [=](uint64_t n) mutable {
                  return ((a0_value.tree_sum() + a2_value.tree_sum()) + n);
                },
                nullptr));
        std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
            _cell->v_mut())
            .a1 = std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<
                 typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
                 std::get<typename mylist<
                     std::function<uint64_t(uint64_t)>>::Mycons>(
                     (*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_depth = d;
        _loop_t = a0_value;
        continue;
      }
    }
  }
  return std::move(*_head);
}
