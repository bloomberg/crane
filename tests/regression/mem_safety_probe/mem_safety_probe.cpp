#include "mem_safety_probe.h"

/// ---- TEST 2: Build list of closures from tree branches ----
/// Each closure captures a tree value via partial application.
/// The closures must survive after the function returns.
MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe::build_adders(
    const MemSafetyProbe::mylist<MemSafetyProbe::tree> &trees) {
  std::shared_ptr<MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>>>
      _head{};
  std::shared_ptr<MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>>>
      *_write = &_head;
  MemSafetyProbe::mylist<MemSafetyProbe::tree> _loop_trees = trees;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe::mylist<MemSafetyProbe::tree>::Mynil>(
            _loop_trees.v())) {
      *_write = std::make_shared<
          MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>>>(
          mylist<std::function<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe::mylist<MemSafetyProbe::tree>::Mycons>(
          _loop_trees.v());
      const MemSafetyProbe::mylist<MemSafetyProbe::tree> &a1_value = *a1;
      auto _cell = std::make_shared<
          MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>>>(
          typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t _x0) mutable -> uint64_t {
                return a0.sum_values(_x0);
              },
              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
               (*_write)->v_mut())
               .a1;
      _loop_trees = a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t MemSafetyProbe::apply_all(
    const MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>> *fns;
  };

  /// _Resume_Mycons: saves [x], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fns});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe::mylist<std::function<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
        _stack.emplace_back(_Resume_Mycons{a0(x)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.x + _result);
    }
  }
  return _result;
}

/// ---- TEST 5: Partial application + match scrutinee reuse ----
/// f captures t by partial application, then t is used as a match
/// scrutinee. The escape analysis must handle this correctly.
uint64_t MemSafetyProbe::match_partial(MemSafetyProbe::tree t) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t _x0) mutable -> uint64_t {
    return t.sum_values(_x0);
  };
  if (std::holds_alternative<typename MemSafetyProbe::tree::Leaf>(t.v_mut())) {
    return f(UINT64_C(0));
  } else {
    auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe::tree::Node>(t.v_mut());
    return f(std::move(a1));
  }
}

/// ---- TEST 6: Deep currying chain ----
/// Multi-level partial application where each level binds a new value.
uint64_t MemSafetyProbe::add3(uint64_t a, uint64_t b, uint64_t c) {
  return ((a + b) + c);
}

/// ---- TEST 7: Store partial application in Box, then apply twice ----
/// The Box stores a closure. If the closure uses & capture,
/// the Box holds dangling references after make_box returns.
MemSafetyProbe::fn_box MemSafetyProbe::make_box(MemSafetyProbe::tree t) {
  return fn_box::box(
      [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); });
}

/// ---- TEST 10: Partial application stored in Box via match ----
/// The partial application captures a match-bound tree value and
/// is stored in a Box. Tests closure escape through constructor inside match.
MemSafetyProbe::fn_box
MemSafetyProbe::box_from_match(const MemSafetyProbe::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe::tree::Leaf>(t.v())) {
    return fn_box::box([](uint64_t n) { return n; });
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MemSafetyProbe::tree::Node>(t.v());
    const MemSafetyProbe::tree &a0_value = *a0;
    return fn_box::box([=](uint64_t _x0) mutable -> uint64_t {
      return a0_value.sum_values(_x0);
    });
  }
}
