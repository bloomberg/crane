#include "mem_safety_probe22.h"

uint64_t MemSafetyProbe22::tree_sum(
    const MemSafetyProbe22::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe22::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified tree_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe22::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 1: Two recursive calls on CHILDREN, but the
/// function takes tree by value because it also returns/stores it.
std::pair<MemSafetyProbe22::tree, uint64_t> MemSafetyProbe22::sum_and_rebuild(
    const MemSafetyProbe22::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe22::tree *a2;
  };

  /// CraneCont_Node_1: saves [a1, pl], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    std::pair<MemSafetyProbe22::tree, uint64_t> pl;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  std::pair<MemSafetyProbe22::tree, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified sum_and_rebuild: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe22::tree &a2 = *_f.a2;
      std::pair<MemSafetyProbe22::tree, uint64_t> pl = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, std::move(pl)});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      std::pair<MemSafetyProbe22::tree, uint64_t> pl = std::move(_f.pl);
      std::pair<MemSafetyProbe22::tree, uint64_t> pr = std::move(_result);
      _result = std::make_pair(
          tree::node(std::move(pl).first, a1, std::move(pr).first),
          ((std::move(pl).second + a1) + std::move(pr).second));
    }
  }
  return _result;
}

/// TEST 2: Function that recurses on children AND stores result
/// in constructor, forcing the tree to be owned.
MemSafetyProbe22::tree MemSafetyProbe22::double_tree(
    const MemSafetyProbe22::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe22::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe22::tree _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe22::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified double_tree: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe22::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), (a1 * UINT64_C(2)),
                           std::move(_result));
    }
  }
  return _result;
}

/// TEST 3: Two recursive calls with child + value in result.
uint64_t MemSafetyProbe22::weighted_sum(
    const MemSafetyProbe22::tree &t,
    uint64_t w) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t w;
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, w], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe22::tree *a2;
    uint64_t w;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, w], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
    uint64_t w;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{w, &t});
  /// Loopified weighted_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t w = _f.w;
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), w});
        _stack.emplace_back(CraneEnter{(w + UINT64_C(1)), crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe22::tree &a2 = *_f.a2;
      uint64_t w = _f.w;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, w});
      _stack.emplace_back(CraneEnter{(w + UINT64_C(1)), &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t w = _f.w;
      _result = ((_f._tmp2 + (a1 * w)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 4: Function with constructed-tree recursive calls.
uint64_t MemSafetyProbe22::split_sum(
    const MemSafetyProbe22::tree &t,
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
    MemSafetyProbe22::tree t;
  };

  /// CraneCont_Node: saves [a1, a2, n_], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe22::tree> a2;
    uint64_t n_;
  };

  /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n, t});
  /// Loopified split_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      const MemSafetyProbe22::tree &t = std::move(_f.t);
      if (n <= 0) {
        _result = tree_sum(t);
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
                t.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename MemSafetyProbe22::tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a1, a2, n_});
          _stack.emplace_back(CraneEnter{
              n_, tree::node(*a0, (a1 + UINT64_C(1)), tree::leaf())});
        }
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe22::tree> a2 = std::move(_f.a2);
      uint64_t n_ = _f.n_;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
      _stack.emplace_back(
          CraneEnter{n_, tree::node(tree::leaf(), (a1 + UINT64_C(1)), *a2)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      _result = (_f._tmp2 + std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Mirror tree (swap children). Two recursive calls.
MemSafetyProbe22::tree MemSafetyProbe22::mirror(
    const MemSafetyProbe22::tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const MemSafetyProbe22::tree *a0;
    uint64_t a1;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe22::tree _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe22::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified mirror: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a0), a1});
        _stack.emplace_back(CraneEnter{crane_raw(a2)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      const MemSafetyProbe22::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a0});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    }
  }
  return _result;
}

/// TEST 7: Insert into BST (non-pointer-safe because constructed tree
/// in recursive call).
MemSafetyProbe22::tree
MemSafetyProbe22::insert(const MemSafetyProbe22::tree &t,
                         uint64_t x) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont1: saves [a1, a2], resumes after recursive call, then processes
  /// rest.
  struct CraneCont1 {
    uint64_t a1;
    std::shared_ptr<MemSafetyProbe22::tree> a2;
  };

  /// CraneCont2: saves [a0, a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont2 {
    std::shared_ptr<MemSafetyProbe22::tree> a0;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  MemSafetyProbe22::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified insert: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        if (x <= a1) {
          _stack.emplace_back(CraneCont1{a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          _stack.emplace_back(CraneCont2{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a1 = _f.a1;
      std::shared_ptr<MemSafetyProbe22::tree> a2 = std::move(_f.a2);
      _result = tree::node(std::move(_result), a1, *a2);
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      std::shared_ptr<MemSafetyProbe22::tree> a0 = std::move(_f.a0);
      uint64_t a1 = _f.a1;
      _result = tree::node(*a0, a1, std::move(_result));
    }
  }
  return _result;
}

MemSafetyProbe22::tree MemSafetyProbe22::insert_all(MemSafetyProbe22::tree t,
                                                    const List<uint64_t> &xs) {
  const List<uint64_t> *_loop_xs = &xs;
  MemSafetyProbe22::tree _loop_t = std::move(t);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
      return _loop_t;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
      _loop_xs = crane_raw(a1);
      _loop_t = insert(std::move(_loop_t), a0);
    }
  }
}

/// TEST 8: Deep tree transformation with two recursive calls.
MemSafetyProbe22::tree MemSafetyProbe22::label_depth(
    const MemSafetyProbe22::tree &t,
    uint64_t d) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t d;
    const MemSafetyProbe22::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2, d], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe22::tree *a2;
    uint64_t d;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, d], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    MemSafetyProbe22::tree _tmp2;
    uint64_t a1;
    uint64_t d;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  MemSafetyProbe22::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{d, &t});
  /// Loopified label_depth: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t d = _f.d;
      const MemSafetyProbe22::tree &t = *_f.t;
      if (std::holds_alternative<typename MemSafetyProbe22::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe22::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), d});
        _stack.emplace_back(CraneEnter{(d + UINT64_C(1)), crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe22::tree &a2 = *_f.a2;
      uint64_t d = _f.d;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, d});
      _stack.emplace_back(CraneEnter{(d + UINT64_C(1)), &a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t d = _f.d;
      _result = tree::node(std::move(_f._tmp2), (a1 + d), std::move(_result));
    }
  }
  return _result;
}
