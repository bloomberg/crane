#include "par_unit_not_concurrent.h"

uint64_t
ParUnitNotConcurrent::sum(const ParUnitNotConcurrent::tree
                              &t) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

  struct CraneEnter {
    const ParUnitNotConcurrent::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const ParUnitNotConcurrent::tree *a2;
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
  /// Loopified sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (crane::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(crane::get<CraneEnter>(_frame));
      const ParUnitNotConcurrent::tree &t = *_f.t;
      if (crane::holds_alternative<typename ParUnitNotConcurrent::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ParUnitNotConcurrent::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(crane::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const ParUnitNotConcurrent::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = ((_f._tmp2 + a1) + std::move(_result));
    }
  }
  return _result;
}

ParUnitNotConcurrent::tree ParUnitNotConcurrent::mk(uint64_t n) {
  std::optional<ParUnitNotConcurrent::tree> _root{};
  crane::shared_box<ParUnitNotConcurrent::tree> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = crane::shared_box<ParUnitNotConcurrent::tree>::make(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = typename ParUnitNotConcurrent::tree::Node(
          nullptr, _loop_n,
          crane::shared_box<ParUnitNotConcurrent::tree>::make(tree::leaf()));
      ParUnitNotConcurrent::tree &_node =
          (_write ? *(*_write =
                          crane::shared_box<ParUnitNotConcurrent::tree>::make(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &crane::get<typename ParUnitNotConcurrent::tree::Node>(_node.v_mut())
               .a0;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

ParUnitNotConcurrent::tree
ParUnitNotConcurrent::mirror(const ParUnitNotConcurrent::tree
                                 &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    const ParUnitNotConcurrent::tree *t;
  };

  /// CraneCont_Node: saves [a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    const ParUnitNotConcurrent::tree *a0;
    uint64_t a1;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    ParUnitNotConcurrent::tree _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  ParUnitNotConcurrent::tree _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified mirror: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (crane::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(crane::get<CraneEnter>(_frame));
      const ParUnitNotConcurrent::tree &t = *_f.t;
      if (crane::holds_alternative<typename ParUnitNotConcurrent::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ParUnitNotConcurrent::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{crane_raw(a0), a1});
        _stack.emplace_back(CraneEnter{crane_raw(a2)});
      }
    } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(crane::get<CraneCont_Node>(_frame));
      const ParUnitNotConcurrent::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a0});
    } else {
      auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    }
  }
  return _result;
}

uint64_t ParUnitNotConcurrent::churn(uint64_t k,
                                     const ParUnitNotConcurrent::tree &t) {
  ParUnitNotConcurrent::tree _loop_t = t;
  uint64_t _loop_k = k;
  while (true) {
    if (_loop_k <= 0) {
      return sum(_loop_t);
    } else {
      uint64_t j = _loop_k - 1;
      _loop_t = mirror(_loop_t);
      _loop_k = j;
    }
  }
}

uint64_t ParUnitNotConcurrent::work(uint64_t k) {
  return (churn(k, shared) + sum(mk(UINT64_C(3000))));
}

uint64_t ParUnitNotConcurrent::race(uint64_t k) {
  std::future<uint64_t> a = std::async(std::launch::async, work, k);
  std::future<uint64_t> b = std::async(std::launch::async, work, k);
  std::future<uint64_t> c = std::async(std::launch::async, work, k);
  std::future<uint64_t> d = std::async(std::launch::async, work, k);
  uint64_t x = std::move(a).get();
  uint64_t y = std::move(b).get();
  uint64_t z = std::move(c).get();
  uint64_t w = std::move(d).get();
  return (((x + y) + z) + w);
}
