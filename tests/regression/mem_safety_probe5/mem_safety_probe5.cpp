#include "mem_safety_probe5.h"

/// TEST 1: Partial app of get_left_val, applied to recursive result.
/// The closure body accesses nested tree structure.
uint64_t MemSafetyProbe5::sum_left_vals(
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l) {
  // Explicit stack replaces the non-tail recursion of sum_left_vals: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> *l;
  };

  struct _after_sum_left_vals_in_Mycons {
    MemSafetyProbe5::tree a0;
  };

  using _frame = std::variant<_call, _after_sum_left_vals_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_after_sum_left_vals_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_left_vals_in_Mycons>(_popped));
      _stack.pop_back();
      MemSafetyProbe5::tree a0 = std::move(_f.a0);
      _result = a0.get_left_val(std::move(_result));
    }
  }
  return _result;
}

/// TEST 2: Build a list of partial apps from trees, then apply all.
/// Each partial app captures a tree with nested structure.
MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe5::build_getters(
    const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>>> *_write =
      nullptr;
  const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mynil>(
            _loop_l->v())) {
      auto _value = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
          _loop_l->v());
      const MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &a1_value = *a1;
      auto _cell = typename MemSafetyProbe5::mylist<
          crane::fn<uint64_t(uint64_t)>>::Mycons(
          [=, a0 = a0](uint64_t _x0) -> uint64_t {
            return a0.get_left_val(_x0);
          },
          nullptr);
      MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe5::mylist<
                          crane::fn<uint64_t(uint64_t)>>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe5::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mycons>(_node.v_mut()).a1;
      _loop_l = &a1_value;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe5::apply_all(
    const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> &l,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of apply_all: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  struct _after_apply_all_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_apply_all_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = x;
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_after_apply_all_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_apply_all_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = a0(std::move(_result));
    }
  }
  return _result;
}

MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe5::collect_left_vals(
    MemSafetyProbe5::tree t,
    MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> acc) {
  // Explicit stack replaces the non-tail recursion of collect_left_vals: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> acc;
    MemSafetyProbe5::tree t;
  };

  struct _after_collect_left_vals_in_Node {
    std::shared_ptr<MemSafetyProbe5::tree> a0;
  };

  using _frame = std::variant<_call, _after_collect_left_vals_in_Node>;
  MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(acc), std::move(t)});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> acc =
          std::move(_f.acc);
      MemSafetyProbe5::tree t = std::move(_f.t);
      if (std::holds_alternative<typename MemSafetyProbe5::tree::Leaf>(
              t.v_mut())) {
        _result = std::move(acc);
      } else {
        auto &[a0, _, a2] =
            std::get<typename MemSafetyProbe5::tree::Node>(t.v_mut());
        const MemSafetyProbe5::tree &a0_value = *a0;
        const MemSafetyProbe5::tree &a2_value = *a2;
        _stack.emplace_back(_after_collect_left_vals_in_Node{a0});
        _stack.emplace_back(_call{mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
            [=](uint64_t _x0) -> uint64_t { return t.get_left_val(_x0); },
            std::move(acc)),
                                  a2_value});
      }
    } else {
      auto _f = std::move(std::get<_after_collect_left_vals_in_Node>(_popped));
      _stack.pop_back();
      std::shared_ptr<MemSafetyProbe5::tree> a0 = std::move(_f.a0);
      const MemSafetyProbe5::tree &a0_value = *a0;
      _stack.emplace_back(_call{std::move(_result), std::move(a0_value)});
    }
  }
  return _result;
}

/// TEST 6: Stress test with very large list of trees.
MemSafetyProbe5::mylist<MemSafetyProbe5::tree>
MemSafetyProbe5::make_tree_list(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>> _root{};
  std::shared_ptr<MemSafetyProbe5::mylist<MemSafetyProbe5::tree>> *_write =
      nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = mylist<MemSafetyProbe5::tree>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe5::mylist<MemSafetyProbe5::tree>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell =
          typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons(
              tree::node(tree::node(tree::leaf(), _loop_n, tree::leaf()),
                         (_loop_n * UINT64_C(2)), tree::leaf()),
              nullptr);
      MemSafetyProbe5::mylist<MemSafetyProbe5::tree> &_node =
          (_write ? *(*_write = std::make_shared<
                          MemSafetyProbe5::mylist<MemSafetyProbe5::tree>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<
              typename MemSafetyProbe5::mylist<MemSafetyProbe5::tree>::Mycons>(
              _node.v_mut())
              .a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe5::sum_getters(
    const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> &l,
    uint64_t x) {
  // Explicit stack replaces the non-tail recursion of sum_getters: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  struct _after_sum_getters_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_sum_getters_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe5::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe5::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe5::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_getters_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_getters_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(x) + std::move(_result));
    }
  }
  return _result;
}
