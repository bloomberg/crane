#include "mem_safety_probe8.h"

/// TEST 1: Non-method tree traversal with double recursion.
/// dummy ensures tree is NOT the first arg (avoiding methodification).
/// tree is the second arg — should be owned if it doesn't escape.
uint64_t MemSafetyProbe8::tree_sum_ext(
    uint64_t _x,
    const MemSafetyProbe8::tree &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
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
  _stack.emplace_back(CraneEnter{&t, _x});
  /// Loopified tree_sum_ext: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 2: Same but with a more complex computation to prevent
/// the optimizer from simplifying.
uint64_t MemSafetyProbe8::tree_weighted(
    uint64_t _x, const MemSafetyProbe8::tree &t,
    uint64_t depth) { /// CraneEnter: captures varying parameters for each
                      /// recursive call.

  struct CraneEnter {
    uint64_t depth;
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// CraneCont_Node: saves [a1, a2, depth], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
    uint64_t depth;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1, depth], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Node_1 {
    uint64_t _tmp2;
    uint64_t a1;
    uint64_t depth;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{depth, &t, _x});
  /// Loopified tree_weighted: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t depth = _f.depth;
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2), depth});
        _stack.emplace_back(
            CraneEnter{(UINT64_C(1) + depth), crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      uint64_t depth = _f.depth;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1, depth});
      _stack.emplace_back(CraneEnter{(UINT64_C(1) + depth), &a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t depth = _f.depth;
      _result = ((_f._tmp2 + (a1 * depth)) + std::move(_result));
    }
  }
  return _result;
}

/// TEST 3: Deep tree traversal — more iterations, more frames.
MemSafetyProbe8::tree MemSafetyProbe8::make_left_spine(uint64_t n) {
  std::optional<MemSafetyProbe8::tree> _root{};
  std::shared_ptr<MemSafetyProbe8::tree> *_write = nullptr;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = std::make_shared<MemSafetyProbe8::tree>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename MemSafetyProbe8::tree::Node(
          nullptr, _loop_n,
          std::make_shared<MemSafetyProbe8::tree>(tree::leaf()));
      MemSafetyProbe8::tree &_node =
          (_write ? *(*_write = std::make_shared<MemSafetyProbe8::tree>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename MemSafetyProbe8::tree::Node>(_node.v_mut()).a0;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

/// TEST 4: Tree traversal where both recursive calls use
/// different subtrees — _After frame must hold one while
/// processing the other.
uint64_t MemSafetyProbe8::tree_collect(
    uint64_t _x,
    const MemSafetyProbe8::tree &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
  };

  /// CraneCont_Node_1: saves [a1, left], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    uint64_t a1;
    uint64_t left;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t, _x});
  /// Loopified tree_collect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      uint64_t left = std::move(_result);
      _stack.emplace_back(CraneCont_Node_1{a1, left});
      _stack.emplace_back(CraneEnter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      uint64_t left = _f.left;
      uint64_t right = std::move(_result);
      _result = ((left + a1) + right);
    }
  }
  return _result;
}

/// TEST 5: Tree function where the tree is consumed (not
/// used after recursive calls) — maximally owned.
uint64_t MemSafetyProbe8::tree_flatten(
    uint64_t _x,
    const MemSafetyProbe8::tree &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const MemSafetyProbe8::tree *t;
    uint64_t _x;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const MemSafetyProbe8::tree *a2;
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
  _stack.emplace_back(CraneEnter{&t, _x});
  /// Loopified tree_flatten: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const MemSafetyProbe8::tree &t = *_f.t;
      uint64_t _x = _f._x;
      if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(t.v())) {
        _result = UINT64_C(1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename MemSafetyProbe8::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0), UINT64_C(0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const MemSafetyProbe8::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2, UINT64_C(0)});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 * a1) * std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Pass tree as a higher-order function argument
/// to prevent methodification completely.
uint64_t MemSafetyProbe8::tree_size_via_fold(const MemSafetyProbe8::tree &t) {
  {
    uint64_t _lc1_x = UINT64_C(0);
    const MemSafetyProbe8::tree &_lc1_t0 = t;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const MemSafetyProbe8::tree *t0;
      uint64_t _x;
    };

    /// CraneCont_Node: saves [a2], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Node {
      const MemSafetyProbe8::tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node_1 {
      uint64_t _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    uint64_t _lc1_result{};
    crane::small_vector<CraneFrame> _lc1_stack;
    _lc1_stack.emplace_back(CraneEnter{&_lc1_t0, _lc1_x});
    /// Loopified go: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_lc1_stack.empty()) {
      CraneFrame _frame = std::move(_lc1_stack.back());
      _lc1_stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const MemSafetyProbe8::tree &_lc1_t0 = *_f.t0;
        uint64_t _lc1_x = _f._x;
        if (std::holds_alternative<typename MemSafetyProbe8::tree::Leaf>(
                _lc1_t0.v())) {
          _lc1_result = UINT64_C(0);
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename MemSafetyProbe8::tree::Node>(_lc1_t0.v());
          _lc1_stack.emplace_back(CraneCont_Node{crane_raw(a2)});
          _lc1_stack.emplace_back(CraneEnter{crane_raw(a0), UINT64_C(0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        const MemSafetyProbe8::tree &a2 = *_f.a2;
        _lc1_stack.emplace_back(CraneCont_Node_1{std::move(_lc1_result)});
        _lc1_stack.emplace_back(CraneEnter{&a2, UINT64_C(0)});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        _lc1_result = ((UINT64_C(1) + _f._tmp2) + std::move(_lc1_result));
      }
    }
    return _lc1_result;
  }
}
