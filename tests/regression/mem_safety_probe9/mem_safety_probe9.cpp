#include "mem_safety_probe9.h"

uint64_t MemSafetyProbe9::sum_fns(
    const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> &l) {
  // Explicit stack replaces the non-tail recursion of sum_fns: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  struct _after_sum_fns_in_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using _frame = std::variant<_call, _after_sum_fns_in_Mycons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe9::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe9::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_after_sum_fns_in_Mycons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_fns_in_Mycons>(_popped));
      _stack.pop_back();
      crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
      _result = (a0(UINT64_C(0)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Collect closures that each capture a subtree.
/// Both l and r are captured AND used in recursive calls.
MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe9::collect_subtree_sums(
    const MemSafetyProbe9::tree &t,
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc) {
  // Explicit stack replaces the non-tail recursion of collect_subtree_sums:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  struct _after_collect_subtree_sums_in_Node {
    const MemSafetyProbe9::tree *a0;
  };

  using _frame = std::variant<_call, _after_collect_subtree_sums_in_Node>;
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(acc), &t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc =
          std::move(_f.acc);
      const MemSafetyProbe9::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe9::tree::Leaf>(t.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe9::tree::Node>(t.v());
        const MemSafetyProbe9::tree &a0_value = *a0;
        const MemSafetyProbe9::tree &a2_value = *a2;
        crane::fn<uint64_t(uint64_t)> f = [=](uint64_t) {
          return ((a0_value.tree_sum() + a1) + a2_value.tree_sum());
        };
        _stack.emplace_back(_after_collect_subtree_sums_in_Node{crane_raw(a0)});
        _stack.emplace_back(_call{mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
            std::move(f), std::move(acc)),
                                  crane_raw(a2)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_collect_subtree_sums_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe9::tree &a0 = *_f.a0;
      const MemSafetyProbe9::tree &a0_value = a0;
      _stack.emplace_back(_call{std::move(_result), &a0_value});
    }
  }
  return _result;
}

/// TEST 2: Similar but each closure captures ONLY the left subtree.
/// The left subtree is shared between closure and recursive call.
MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe9::collect_left_sums(
    const MemSafetyProbe9::tree &t,
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc) {
  // Explicit stack replaces the non-tail recursion of collect_left_sums: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  struct _after_collect_left_sums_in_Node {
    const MemSafetyProbe9::tree *a0;
  };

  using _frame = std::variant<_call, _after_collect_left_sums_in_Node>;
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(acc), &t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc =
          std::move(_f.acc);
      const MemSafetyProbe9::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe9::tree::Leaf>(t.v())) {
        _result = std::move(acc);
      } else {
        const auto &[a0, _, a2] =
            std::get<typename MemSafetyProbe9::tree::Node>(t.v());
        const MemSafetyProbe9::tree &a0_value = *a0;
        const MemSafetyProbe9::tree &a2_value = *a2;
        crane::fn<uint64_t(uint64_t)> f =
            [=](uint64_t) { return a0_value.tree_sum(); };
        _stack.emplace_back(_after_collect_left_sums_in_Node{crane_raw(a0)});
        _stack.emplace_back(_call{mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
            std::move(f), std::move(acc)),
                                  crane_raw(a2)});
      }
    } else {
      auto _f = std::move(std::get<_after_collect_left_sums_in_Node>(_popped));
      _stack.pop_back();
      const MemSafetyProbe9::tree &a0 = *_f.a0;
      const MemSafetyProbe9::tree &a0_value = a0;
      _stack.emplace_back(_call{std::move(_result), &a0_value});
    }
  }
  return _result;
}

/// TEST 3: Build closures from list where each closure
/// captures the tail and a computed value.
MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe9::list_accum_closures(
    const MemSafetyProbe9::mylist<uint64_t> &l,
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _loop_acc =
      std::move(acc);
  const MemSafetyProbe9::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe9::mylist<uint64_t>::Mynil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe9::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      const MemSafetyProbe9::mylist<uint64_t> &a1_value = *a1;
      uint64_t tail_len = a1_value.length();
      crane::fn<uint64_t(uint64_t)> f =
          [=](uint64_t) { return (a0 * tail_len); };
      _loop_acc = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          std::move(f), std::move(_loop_acc));
      _loop_l = &a1_value;
    }
  }
}

/// TEST 6: Stress test — large tree, many closures.
MemSafetyProbe9::tree MemSafetyProbe9::make_balanced(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of make_balanced: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_make_balanced_in_S {
    uint64_t n;
    uint64_t n_;
  };

  struct _after_make_balanced_in_S_2 {
    uint64_t n;
    MemSafetyProbe9::tree _tmp2;
  };

  using _frame = std::variant<_call, _after_make_balanced_in_S,
                              _after_make_balanced_in_S_2>;
  MemSafetyProbe9::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_after_make_balanced_in_S{n, n_});
        _stack.emplace_back(_call{n_});
      }
    } else if (std::holds_alternative<_after_make_balanced_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_make_balanced_in_S>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(_after_make_balanced_in_S_2{n, std::move(_result)});
      _stack.emplace_back(_call{n_});
    } else {
      auto _f = std::move(std::get<_after_make_balanced_in_S_2>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      _result = tree::node(std::move(_f._tmp2), n, std::move(_result));
    }
  }
  return _result;
}
