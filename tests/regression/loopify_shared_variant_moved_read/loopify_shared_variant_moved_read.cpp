#include "loopify_shared_variant_moved_read.h"

LoopifySharedVariantMovedRead::tree
LoopifySharedVariantMovedRead::g(const List<uint64_t> &l) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto k =
      crane::immortal(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()));
  static const auto k_1 =
      crane::immortal(List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()));

  // Explicit stack replaces the non-tail recursion of g: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_g_in_Cons {};

  using _frame = std::variant<_call, _after_g_in_Cons>;
  LoopifySharedVariantMovedRead::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (crane::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = tree::leaf();
      } else {
        const auto &[_, a1] = crane::get<typename List<uint64_t>::Cons>(l.v());
        const List<uint64_t> &a1_value = *a1;
        if (crane::holds_alternative<typename List<uint64_t>::Nil>(a1_value.v())) {
          _result = k_1.template fold_left<LoopifySharedVariantMovedRead::tree>(
              [](LoopifySharedVariantMovedRead::tree acc,
                 uint64_t) { return acc; },
              k);
        } else {
          _stack.emplace_back(_after_g_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(crane::get<_after_g_in_Cons>(_popped));
      _stack.pop_back();
      _result = k_1.template fold_left<LoopifySharedVariantMovedRead::tree>(
          [](LoopifySharedVariantMovedRead::tree acc, uint64_t) { return acc; },
          std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifySharedVariantMovedRead::size(
    const LoopifySharedVariantMovedRead::tree &t) {
  // Explicit stack replaces the non-tail recursion of size: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifySharedVariantMovedRead::tree *t;
  };

  struct _after_size_in_Node {
    const LoopifySharedVariantMovedRead::tree *r;
  };

  struct _after_size_in_Node_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_size_in_Node, _after_size_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const LoopifySharedVariantMovedRead::tree &t = *_f.t;
      if (crane::holds_alternative<
              typename LoopifySharedVariantMovedRead::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[l, _, r] =
            crane::get<typename LoopifySharedVariantMovedRead::tree::Node>(
                t.v());
        _stack.emplace_back(_after_size_in_Node{crane_raw(r)});
        _stack.emplace_back(_call{crane_raw(l)});
      }
    } else if (crane::holds_alternative<_after_size_in_Node>(_popped)) {
      auto _f = std::move(crane::get<_after_size_in_Node>(_popped));
      _stack.pop_back();
      const LoopifySharedVariantMovedRead::tree &r = *_f.r;
      _stack.emplace_back(_after_size_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{&r});
    } else {
      auto _f = std::move(crane::get<_after_size_in_Node_2>(_popped));
      _stack.pop_back();
      _result = ((_f._tmp2 + std::move(_result)) + 1);
    }
  }
  return _result;
}
