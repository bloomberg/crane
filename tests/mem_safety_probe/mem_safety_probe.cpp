#include "mem_safety_probe.h"

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
  crane::small_vector<_Frame> _stack;
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
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.x + std::move(_result));
    }
  }
  return _result;
}

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

uint64_t MemSafetyProbe::add3(uint64_t a, uint64_t b, uint64_t c) {
  return ((a + b) + c);
}

MemSafetyProbe::fn_box MemSafetyProbe::make_box(MemSafetyProbe::tree t) {
  return fn_box::box(
      [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); });
}

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
