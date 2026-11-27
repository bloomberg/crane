#include "loopify_final_move.h"

std::pair<final_move_support::buffer, uint64_t>
LoopifyFinalMove::thread_end(final_move_support::buffer b, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of thread_end: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
  };

  struct _after_thread_end_in_S {
    uint64_t k;
  };

  using _frame = std::variant<_call, _after_thread_end_in_S>;
  std::pair<final_move_support::buffer, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = std::make_pair(
            final_move_support::push(std::move(b), UINT64_C(7)), UINT64_C(0));
      } else {
        uint64_t k_ = k - 1;
        _stack.emplace_back(_after_thread_end_in_S{k});
        _stack.emplace_back(_call{k_});
      }
    } else {
      auto _f = std::move(std::get<_after_thread_end_in_S>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      auto [b_, n] = std::move(_result);
      _result = std::make_pair(std::move(b_), k + n);
    }
  }
  return _result;
}

std::pair<final_move_support::buffer, uint64_t>
LoopifyFinalMove::thread_both(final_move_support::buffer b, uint64_t k) {
  // Explicit stack replaces the non-tail recursion of thread_both: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t k;
  };

  struct _after_thread_both_in_S {
    uint64_t k;
  };

  using _frame = std::variant<_call, _after_thread_both_in_S>;
  std::pair<final_move_support::buffer, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{k});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      if (k <= 0) {
        _result = std::make_pair(final_move_support::push(b, UINT64_C(7)),
                                 UINT64_C(0));
      } else {
        uint64_t k_ = k - 1;
        _stack.emplace_back(_after_thread_both_in_S{k});
        _stack.emplace_back(_call{k_});
      }
    } else {
      auto _f = std::move(std::get<_after_thread_both_in_S>(_popped));
      _stack.pop_back();
      uint64_t k = _f.k;
      auto [b_, n] = std::move(_result);
      _result = std::make_pair(
          std::move(b_), k + n + (static_cast<std::uint64_t>(b.items.size())));
    }
  }
  return _result;
}

List<final_move_support::buffer>
LoopifyFinalMove::thread_tree(final_move_support::buffer b, const Tree &t) {
  // Explicit stack replaces the non-tail recursion of thread_tree: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const Tree *t;
  };

  struct _after_thread_tree_in_Node {
    const Tree *a1;
  };

  struct _after_thread_tree_in_Node_2 {
    List<final_move_support::buffer> _tmp2;
  };

  using _frame = std::variant<_call, _after_thread_tree_in_Node,
                              _after_thread_tree_in_Node_2>;
  List<final_move_support::buffer> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Tree &t = *_f.t;
      if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
        const auto &[a0] = std::get<typename Tree::Leaf>(t.v());
        _result = List<final_move_support::buffer>::cons(
            final_move_support::push(b, a0),
            List<final_move_support::buffer>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename Tree::Node>(t.v());
        _stack.emplace_back(_after_thread_tree_in_Node{crane_raw(a1)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_thread_tree_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_thread_tree_in_Node>(_popped));
      _stack.pop_back();
      const Tree &a1 = *_f.a1;
      _stack.emplace_back(_after_thread_tree_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&a1});
    } else {
      auto _f = std::move(std::get<_after_thread_tree_in_Node_2>(_popped));
      _stack.pop_back();
      _result = _f._tmp2.app(std::move(_result));
    }
  }
  return _result;
}
