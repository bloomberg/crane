#include "mem_safety_probe15.h"

uint64_t
MemSafetyProbe15::sum_list(const MemSafetyProbe15::mylist<uint64_t>
                               &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe15::mylist<uint64_t> *l;
  };

  /// CraneCont_Mycons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Mycons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified sum_list: CraneEnter -> CraneCont_Mycons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe15::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe15::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe15::mylist<uint64_t>::Mycons>(
                l.v());
        _stack.emplace_back(CraneCont_Mycons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Tree flattening where left subtree is used AFTER
/// right subtree recursive call.
/// In loopified code, the Enter frame for the right subtree
/// may move the left subtree's pointer.
MemSafetyProbe15::mylist<uint64_t> MemSafetyProbe15::flatten(
    const MemSafetyProbe15::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe15::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified flatten: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = std::move(_f._tmp2).myapp(
          mylist<uint64_t>::mycons(a1, std::move(_result)));
    }
  }
  return _result;
}

/// TEST 2: Tree to list where each element is the sum of
/// its subtree. Uses both subtrees for computation AND recursion.
MemSafetyProbe15::mylist<uint64_t> MemSafetyProbe15::subtree_sums(
    const MemSafetyProbe15::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe15::tree *t;
  };

  /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe15::mylist<uint64_t> _tmp2;
    std::shared_ptr<MemSafetyProbe15::tree> a0;
    uint64_t a1;
    const MemSafetyProbe15::tree *a2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe15::mylist<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified subtree_sums: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe15::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe15::tree::Leaf>(
              t.v())) {
        _result = mylist<uint64_t>::mynil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe15::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _stack.emplace_back(
          CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      std::shared_ptr<MemSafetyProbe15::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      const MemSafetyProbe15::tree &a2 = *_f.a2;
      _result = mylist<uint64_t>::mycons(
          ((a0->tree_sum() + a1) + a2.tree_sum()),
          std::move(_f._tmp2).myapp(std::move(_result)));
    }
  }
  return _result;
}

/// TEST 5: Deep left-spine tree.
/// Stresses the frame stack depth.
MemSafetyProbe15::tree MemSafetyProbe15::left_spine(uint64_t n) {
  std::shared_ptr<MemSafetyProbe15::tree> _head{};
  std::shared_ptr<MemSafetyProbe15::tree> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe15::tree>(tree::leaf());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe15::tree>(
          typename MemSafetyProbe15::tree::Node(
              nullptr, _loop_n,
              std::make_shared<MemSafetyProbe15::tree>(tree::leaf())));
      *_write = std::move(_cell);
      _write =
          &std::get<typename MemSafetyProbe15::tree::Node>((*_write)->v_mut())
               .a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 9: Build a large tree and verify all values are preserved.
MemSafetyProbe15::tree MemSafetyProbe15::make_tree(
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
    MemSafetyProbe15::tree _tmp2;
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n_, CraneCont_n__1>;
  MemSafetyProbe15::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified make_tree: CraneEnter -> CraneCont_n_ -> CraneCont_n__1.
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
