#include "mem_safety_probe.h"

/// ---- TEST 2: Build list of closures from tree branches ----
/// Each closure captures a tree value via partial application.
/// The closures must survive after the function returns.
MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe::build_adders(
    const MemSafetyProbe::mylist<MemSafetyProbe::tree> &trees) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>>> *_write =
      nullptr;
  const MemSafetyProbe::mylist<MemSafetyProbe::tree> *_loop_trees = &trees;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe::mylist<MemSafetyProbe::tree>::Mynil>(
            _loop_trees->v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe::mylist<MemSafetyProbe::tree>::Mycons>(
          _loop_trees->v());
      const MemSafetyProbe::mylist<MemSafetyProbe::tree> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons(
          [=](uint64_t _x0) -> uint64_t { return a0.sum_values(_x0); },
          nullptr);
      MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (
              _write ? *(*_write = std::make_shared<MemSafetyProbe::mylist<
                             crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                     : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut()).a1;
      _loop_trees = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe::apply_all(
    const MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of apply_all: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>> *fns;
  };

  struct _after_apply_all_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_apply_all_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&fns});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe::mylist<crane::fn<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(fns.v());
        _stack.emplace_back(_after_apply_all_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_apply_all_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(x) + std::move(_result));
    }
  }
  return _result;
}

/// ---- TEST 5: Partial application + match scrutinee reuse ----
/// f captures t by partial application, then t is used as a match
/// scrutinee. The escape analysis must handle this correctly.
uint64_t MemSafetyProbe::match_partial(MemSafetyProbe::tree t) {
  crane::fn<uint64_t(uint64_t)> f =
      [=](uint64_t _x0) -> uint64_t { return t.sum_values(_x0); };
  if (std::holds_alternative<typename MemSafetyProbe::tree::Leaf>(t.v_mut())) {
    return f(UINT64_C(0));
  } else {
    auto &[_, a1, _] = std::get<typename MemSafetyProbe::tree::Node>(t.v_mut());
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
  return fn_box::box([=, t = std::move(t)](uint64_t _x0) -> uint64_t {
    return t.sum_values(_x0);
  });
}

/// ---- TEST 10: Partial application stored in Box via match ----
/// The partial application captures a match-bound tree value and
/// is stored in a Box. Tests closure escape through constructor inside match.
MemSafetyProbe::fn_box
MemSafetyProbe::box_from_match(const MemSafetyProbe::tree &t) {
  if (std::holds_alternative<typename MemSafetyProbe::tree::Leaf>(t.v())) {
    return fn_box::box([](uint64_t n) { return n; });
  } else {
    const auto &[a0, _, _] =
        std::get<typename MemSafetyProbe::tree::Node>(t.v());
    const MemSafetyProbe::tree &a0_value = *a0;
    return fn_box::box(
        [=](uint64_t _x0) -> uint64_t { return a0_value.sum_values(_x0); });
  }
}
