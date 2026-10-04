#include "mem_safety_probe9.h"

uint64_t MemSafetyProbe9::sum_fns(
    const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
        &l) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    crane::fn<uint64_t(uint64_t)> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_fns: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe9::mylist<
              crane::fn<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe9::mylist<
            crane::fn<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
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
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
        acc) { /// CraneEnter: captures varying parameters for each recursive
               /// call.

  struct CraneEnter {
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  /// CraneCont_Node: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe9::tree> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(acc), &t});
  /// Loopified collect_subtree_sums: CraneEnter -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
        _stack.emplace_back(CraneCont_Node{a0});
        _stack.emplace_back(
            CraneEnter{mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
                           std::move(f), std::move(acc)),
                       crane_raw(a2)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe9::tree> a0 = std::move(_f.a0);
      const MemSafetyProbe9::tree &a0_value = *a0;
      _stack.emplace_back(CraneEnter{std::move(_result), crane_raw(a0)});
    }
  }
  return _result;
}

/// TEST 2: Similar but each closure captures ONLY the left subtree.
/// The left subtree is shared between closure and recursive call.
MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
MemSafetyProbe9::collect_left_sums(
    const MemSafetyProbe9::tree &t,
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>>
        acc) { /// CraneEnter: captures varying parameters for each recursive
               /// call.

  struct CraneEnter {
    MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> acc;
    const MemSafetyProbe9::tree *t;
  };

  /// CraneCont_Node: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe9::tree> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(acc), &t});
  /// Loopified collect_left_sums: CraneEnter -> CraneCont_Node.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          return a0_value.tree_sum();
        };
        _stack.emplace_back(CraneCont_Node{a0});
        _stack.emplace_back(
            CraneEnter{mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
                           std::move(f), std::move(acc)),
                       crane_raw(a2)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe9::tree> a0 = std::move(_f.a0);
      const MemSafetyProbe9::tree &a0_value = *a0;
      _stack.emplace_back(CraneEnter{std::move(_result), crane_raw(a0)});
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
  MemSafetyProbe9::mylist<crane::fn<uint64_t(uint64_t)>> _loop_acc =
      std::move(acc);
  MemSafetyProbe9::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe9::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe9::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe9::mylist<uint64_t> &a1_value = *a1;
      uint64_t tail_len = a1_value.length();
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t) {
        return (a0 * tail_len);
      };
      _loop_acc = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
          std::move(f), std::move(_loop_acc));
      _loop_l = a1_value;
    }
  }
}

/// TEST 6: Stress test — large tree, many closures.
MemSafetyProbe9::tree MemSafetyProbe9::make_balanced(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n_: saves [n, n_], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n_ {
    uint64_t n;
    uint64_t n_;
  };

  /// CraneCont_n__1: saves [_tmp2, n], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_n__1 {
    MemSafetyProbe9::tree _tmp2;
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_, CraneCont_n__1>;
  MemSafetyProbe9::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified make_balanced: CraneEnter -> CraneCont_n_ -> CraneCont_n__1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree::leaf();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(CraneCont_n_{n, n_});
        _stack.emplace_back(CraneEnter{n_});
      }
    } else if (std::holds_alternative<CraneCont_n_>(_frame)) {
      auto _f = std::move(std::get<CraneCont_n_>(_frame));
      uint64_t n = _f.n;
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_n__1{std::move(_result), n});
      _stack.emplace_back(CraneEnter{n_});
    } else {
      auto _f = std::move(std::get<CraneCont_n__1>(_frame));
      uint64_t n = _f.n;
      _result = tree::node(std::move(_f._tmp2), n, std::move(_result));
    }
  }
  return _result;
}
