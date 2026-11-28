#include "par_unit_not_concurrent.h"

uint64_t ParUnitNotConcurrent::sum(const ParUnitNotConcurrent::tree &t) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const ParUnitNotConcurrent::tree *t;
  };

  struct _after_sum_in_Node {
    uint64_t a1;
    const ParUnitNotConcurrent::tree *a2;
  };

  struct _after_sum_in_Node_2 {
    uint64_t a1;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _after_sum_in_Node, _after_sum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const ParUnitNotConcurrent::tree &t = *_f.t;
      if (crane::holds_alternative<typename ParUnitNotConcurrent::tree::Leaf>(
              t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ParUnitNotConcurrent::tree::Node>(t.v());
        _stack.emplace_back(_after_sum_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (crane::holds_alternative<_after_sum_in_Node>(_popped)) {
      auto _f = std::move(crane::get<_after_sum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const ParUnitNotConcurrent::tree &a2 = *_f.a2;
      _stack.emplace_back(_after_sum_in_Node_2{a1, _result});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(crane::get<_after_sum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2 + a1 + _result;
    }
  }
  return _result;
}

ParUnitNotConcurrent::tree ParUnitNotConcurrent::mk(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<ParUnitNotConcurrent::tree> _root{};
  crane::shared_box<ParUnitNotConcurrent::tree> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = tree::leaf();
      (_write ? *(*_write = crane::shared_box<ParUnitNotConcurrent::tree>::make(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = n - 1;
      auto _cell = typename ParUnitNotConcurrent::tree::Node(
          nullptr, n,
          crane::shared_box<ParUnitNotConcurrent::tree>::make(tree::leaf()));
      ParUnitNotConcurrent::tree &_node =
          (_write ? *(*_write =
                          crane::shared_box<ParUnitNotConcurrent::tree>::make(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &crane::get<typename ParUnitNotConcurrent::tree::Node>(_node.v_mut()).a0;
      n = m;
      continue;
    }
  }
  return std::move(*_root);
}

ParUnitNotConcurrent::tree
ParUnitNotConcurrent::mirror(const ParUnitNotConcurrent::tree &t) {
  // Explicit stack replaces the non-tail recursion of mirror: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const ParUnitNotConcurrent::tree *t;
  };

  struct _after_mirror_in_Node {
    const ParUnitNotConcurrent::tree *a0;
    uint64_t a1;
  };

  struct _after_mirror_in_Node_2 {
    uint64_t a1;
    ParUnitNotConcurrent::tree _tmp2;
  };

  using _frame =
      std::variant<_call, _after_mirror_in_Node, _after_mirror_in_Node_2>;
  ParUnitNotConcurrent::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const ParUnitNotConcurrent::tree &t = *_f.t;
      if (crane::holds_alternative<typename ParUnitNotConcurrent::tree::Leaf>(
              t.v())) {
        _result = tree::leaf();
      } else {
        const auto &[a0, a1, a2] =
            crane::get<typename ParUnitNotConcurrent::tree::Node>(t.v());
        _stack.emplace_back(_after_mirror_in_Node{crane_raw(a0), a1});
        _stack.emplace_back(_call{crane_raw(a2)});
      }
    } else if (crane::holds_alternative<_after_mirror_in_Node>(_popped)) {
      auto _f = std::move(crane::get<_after_mirror_in_Node>(_popped));
      _stack.pop_back();
      const ParUnitNotConcurrent::tree &a0 = *_f.a0;
      uint64_t a1 = _f.a1;
      _stack.emplace_back(_after_mirror_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a0});
    } else {
      auto _f = std::move(crane::get<_after_mirror_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = tree::node(std::move(_f._tmp2), a1, std::move(_result));
    }
  }
  return _result;
}

uint64_t ParUnitNotConcurrent::churn(uint64_t k,
                                     const ParUnitNotConcurrent::tree &t) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  ParUnitNotConcurrent::tree _loop_t = t;
  while (true) {
    if (k <= 0) {
      return sum(_loop_t);
    } else {
      uint64_t j = k - 1;
      _loop_t = mirror(std::move(_loop_t));
      k = j;
    }
  }
}

uint64_t ParUnitNotConcurrent::work(uint64_t k) {
  return churn(k, shared) + sum(mk(UINT64_C(3000)));
}

uint64_t ParUnitNotConcurrent::race(uint64_t k) {
  std::shared_future<uint64_t> a =
      std::async(std::launch::async, work, k).share();
  std::shared_future<uint64_t> b =
      std::async(std::launch::async, work, k).share();
  std::shared_future<uint64_t> c =
      std::async(std::launch::async, work, k).share();
  std::shared_future<uint64_t> d =
      std::async(std::launch::async, work, k).share();
  uint64_t x = a.get();
  uint64_t y = b.get();
  uint64_t z = c.get();
  uint64_t w = d.get();
  return x + y + z + w;
}
