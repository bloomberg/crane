#include "gb_bst.h"

uint64_t GbBst::next(uint64_t s) {
  auto &&_once1 = ((s * UINT64_C(75)) + UINT64_C(74));
  auto &&_once2 = UINT64_C(65537);
  return (_once2 ? _once1 % _once2 : _once1);
}

List<uint64_t> GbBst::randoms(uint64_t n, uint64_t s) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_s, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = next(_loop_s);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

GbBst::tree GbBst::insert(uint64_t x, const GbBst::tree &t) {
  // Explicit stack replaces the non-tail recursion of insert: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const GbBst::tree *t;
  };

  struct _after_insert_in_true {
    uint64_t k0;
    std::shared_ptr<GbBst::tree> r0;
  };

  struct _after_insert_in_true_2 {
    std::shared_ptr<GbBst::tree> l0;
    uint64_t k0;
  };

  using _frame =
      std::variant<_call, _after_insert_in_true, _after_insert_in_true_2>;
  GbBst::tree _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const GbBst::tree &t = *_f.t;
      if (std::holds_alternative<typename GbBst::tree::Leaf>(t.v())) {
        _result = tree::node(tree::leaf(), x, tree::leaf());
      } else {
        const auto &[l0, k0, r0] = std::get<typename GbBst::tree::Node>(t.v());
        if (x < k0) {
          _stack.emplace_back(_after_insert_in_true{k0, r0});
          _stack.emplace_back(_call{crane_raw(l0)});
        } else {
          if (k0 < x) {
            _stack.emplace_back(_after_insert_in_true_2{l0, k0});
            _stack.emplace_back(_call{crane_raw(r0)});
          } else {
            _result = std::move(t);
          }
        }
      }
    } else if (std::holds_alternative<_after_insert_in_true>(_popped)) {
      auto _f = std::move(std::get<_after_insert_in_true>(_popped));
      _stack.pop_back();
      uint64_t k0 = _f.k0;
      std::shared_ptr<GbBst::tree> r0 = std::move(_f.r0);
      _result = tree::node(std::move(_result), k0, crane::shared_child(r0));
    } else {
      auto _f = std::move(std::get<_after_insert_in_true_2>(_popped));
      _stack.pop_back();
      std::shared_ptr<GbBst::tree> l0 = std::move(_f.l0);
      uint64_t k0 = _f.k0;
      _result = tree::node(crane::shared_child(l0), k0, std::move(_result));
    }
  }
  return _result;
}

uint64_t GbBst::tsum(const GbBst::tree &t) {
  // Explicit stack replaces the non-tail recursion of tsum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const GbBst::tree *t;
  };

  struct _after_tsum_in_Node {
    uint64_t k0;
    const GbBst::tree *r0;
  };

  struct _after_tsum_in_Node_2 {
    uint64_t k0;
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_tsum_in_Node, _after_tsum_in_Node_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const GbBst::tree &t = *_f.t;
      if (std::holds_alternative<typename GbBst::tree::Leaf>(t.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[l0, k0, r0] = std::get<typename GbBst::tree::Node>(t.v());
        _stack.emplace_back(_after_tsum_in_Node{k0, crane_raw(r0)});
        _stack.emplace_back(_call{crane_raw(l0)});
      }
    } else if (std::holds_alternative<_after_tsum_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_tsum_in_Node>(_popped));
      _stack.pop_back();
      uint64_t k0 = _f.k0;
      const GbBst::tree &r0 = *_f.r0;
      _stack.emplace_back(_after_tsum_in_Node_2{k0, std::move(_result)});
      _stack.emplace_back(_call{&r0});
    } else {
      auto _f = std::move(std::get<_after_tsum_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t k0 = _f.k0;
      _result = ((_f._tmp2 + k0) + std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> GbBst::to_list(const GbBst::tree &t, List<uint64_t> acc) {
  // Explicit stack replaces the non-tail recursion of to_list: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> acc;
    const GbBst::tree *t;
  };

  struct _after_to_list_in_Node {
    const GbBst::tree *l0;
    uint64_t k0;
  };

  using _frame = std::variant<_call, _after_to_list_in_Node>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{std::move(acc), &t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      List<uint64_t> acc = std::move(_f.acc);
      const GbBst::tree &t = *_f.t;
      if (std::holds_alternative<typename GbBst::tree::Leaf>(t.v())) {
        _result = std::move(acc);
      } else {
        const auto &[l0, k0, r0] = std::get<typename GbBst::tree::Node>(t.v());
        _stack.emplace_back(_after_to_list_in_Node{crane_raw(l0), k0});
        _stack.emplace_back(_call{std::move(acc), crane_raw(r0)});
      }
    } else {
      auto _f = std::move(std::get<_after_to_list_in_Node>(_popped));
      _stack.pop_back();
      const GbBst::tree &l0 = *_f.l0;
      uint64_t k0 = _f.k0;
      _stack.emplace_back(
          _call{List<uint64_t>::cons(k0, std::move(_result)), &l0});
    }
  }
  return _result;
}

uint64_t GbBst::bst(uint64_t n, uint64_t rounds) {
  GbBst::tree t =
      randoms(n, UINT64_C(7)).template fold_left<GbBst::tree>(
          [](const GbBst::tree &t0, uint64_t x) { return insert(x, t0); },
          tree::leaf());
  return (
      ListDef::seq(UINT64_C(0), rounds).template fold_left<uint64_t>(
          [=](uint64_t acc, uint64_t i) {
            return (acc + tsum(tmap([=](uint64_t k) { return (k + i); }, t)));
          },
          UINT64_C(0)) +
      to_list(t, List<uint64_t>::nil()).length());
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
