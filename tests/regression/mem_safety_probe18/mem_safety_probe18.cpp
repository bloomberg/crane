#include "mem_safety_probe18.h"

uint64_t
MemSafetyProbe18::sum_list(const MemSafetyProbe18::mylist<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_list: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe18::mylist<uint64_t> *l;
  };

  struct _after_sum_list_in_Mycons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe18::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_list_in_Mycons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = a0 + _result;
    }
  }
  return _result;
}

/// TEST 5: Complex fold that builds a tree from a list.
MemSafetyProbe18::tree
MemSafetyProbe18::fold_left_tree(const MemSafetyProbe18::mylist<uint64_t> &l,
                                 MemSafetyProbe18::tree acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe18::tree _loop_acc = std::move(acc);
  const MemSafetyProbe18::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe18::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe18::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      _loop_acc = tree::node(std::move(_loop_acc), a0, tree::leaf());
      _loop_l = crane_raw(a1);
    }
  }
}

/// TEST 8: Nested constructor building: build a list of trees
/// using the same tree in different positions.
MemSafetyProbe18::mylist<MemSafetyProbe18::tree>
MemSafetyProbe18::build_tree_list(const MemSafetyProbe18::tree &t, uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> _root{};
  std::shared_ptr<MemSafetyProbe18::mylist<MemSafetyProbe18::tree>> *_write =
      nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = mylist<MemSafetyProbe18::tree>::mynil();
      (_write ? *(*_write = std::make_shared<
                      MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = n - 1;
      auto _cell =
          typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons(
              tree::node(t, n, tree::leaf()), nullptr);
      MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &_node =
          (_write ? *(*_write = std::make_shared<
                          MemSafetyProbe18::mylist<MemSafetyProbe18::tree>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<
              typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons>(
              _node.v_mut())
              .a1;
      n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t MemSafetyProbe18::sum_tree_list(
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &l) {
  // Explicit stack replaces the non-tail recursion of sum_tree_list: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> *l;
  };

  struct _after_sum_tree_list_in_Mycons {
    MemSafetyProbe18::tree a0;
  };

  using _frame = std::variant<_call, _after_sum_tree_list_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe18::mylist<MemSafetyProbe18::tree> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mynil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<
            typename MemSafetyProbe18::mylist<MemSafetyProbe18::tree>::Mycons>(
            l.v());
        _stack.emplace_back(_after_sum_tree_list_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_tree_list_in_Mycons>(_popped));
      _stack.pop_back();
      MemSafetyProbe18::tree a0 = std::move(_f.a0);
      _result = a0.tree_sum() + _result;
    }
  }
  return _result;
}
