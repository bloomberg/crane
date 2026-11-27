#include "loopify_special_recursion.h"

List<uint64_t>
LoopifySpecialRecursion::process_twice_fuel(uint64_t fuel,
                                            const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of process_twice_fuel: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> l;
    uint64_t fuel;
  };

  struct _after_process_twice_fuel_in_Cons {
    uint64_t fuel_;
    uint64_t a0;
  };

  struct _after_process_twice_fuel_in_Cons_2 {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_process_twice_fuel_in_Cons,
                              _after_process_twice_fuel_in_Cons_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{l, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = _f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_after_process_twice_fuel_in_Cons{fuel_, a0});
          _stack.emplace_back(_call{*a1, fuel_});
        }
      }
    } else if (
            std::holds_alternative<_after_process_twice_fuel_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_process_twice_fuel_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t fuel_ = _f.fuel_;
      uint64_t a0 = _f.a0;
      List<uint64_t> first = std::move(_result);
      _stack.emplace_back(_after_process_twice_fuel_in_Cons_2{a0});
      _stack.emplace_back(_call{std::move(first), fuel_});
    } else {
      auto _f =
          std::move(std::get<_after_process_twice_fuel_in_Cons_2>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<uint64_t> second = std::move(_result);
      _result = List<uint64_t>::cons(a0, std::move(second));
    }
  }
  return _result;
}

List<uint64_t> LoopifySpecialRecursion::process_twice(const List<uint64_t> &l) {
  return process_twice_fuel((l.length() * l.length()), l);
}

List<uint64_t> LoopifySpecialRecursion::double_append(const List<uint64_t> &l1,
                                                      List<uint64_t> l2) {
  // Explicit stack replaces the non-tail recursion of double_append: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l1;
  };

  struct _after_double_append_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_double_append_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l1});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = l2;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_after_double_append_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_double_append_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(a0, rest.app(rest));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySpecialRecursion::remove_if_sum_even(const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t next_val = [&]() {
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a00, _] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          return a00;
        }
      }();
      if ((UINT64_C(2) ? (a0 + next_val) % UINT64_C(2) : (a0 + next_val)) ==
          UINT64_C(0)) {
        _loop_l = crane_raw(a1);
        continue;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t>
LoopifySpecialRecursion::reverse_insert(uint64_t x, const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (a0 < x) {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        auto _value = List<uint64_t>::cons(x, crane::shared_child(_loop_l));
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySpecialRecursion::collect_sorted(
    const LoopifySpecialRecursion::tree &t) {
  // Explicit stack replaces the non-tail recursion of collect_sorted: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifySpecialRecursion::tree *t;
  };

  struct _after_collect_sorted_in_Node {
    uint64_t a1;
    const LoopifySpecialRecursion::tree *a2;
  };

  struct _after_collect_sorted_in_Node_2 {
    uint64_t a1;
    List<uint64_t> _tmp2;
  };

  using _frame = std::variant<_call, _after_collect_sorted_in_Node,
                              _after_collect_sorted_in_Node_2>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&t});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifySpecialRecursion::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifySpecialRecursion::tree::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifySpecialRecursion::tree::Node>(t.v());
        _stack.emplace_back(_after_collect_sorted_in_Node{a1, crane_raw(a2)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_collect_sorted_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_collect_sorted_in_Node>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      const LoopifySpecialRecursion::tree &a2 = *_f.a2;
      _stack.emplace_back(
          _after_collect_sorted_in_Node_2{a1, std::move(_result)});
      _stack.emplace_back(_call{&a2});
    } else {
      auto _f = std::move(std::get<_after_collect_sorted_in_Node_2>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = _f._tmp2.app(List<uint64_t>::cons(a1, std::move(_result)));
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices_aux(const List<uint64_t> &l,
                                                      uint64_t idx) {
  // Explicit stack replaces the non-tail recursion of sum_odd_indices_aux:
  // _call frames are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t idx;
    const List<uint64_t> *l;
  };

  struct _after_sum_odd_indices_aux_in_true {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_odd_indices_aux_in_true>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{idx, &l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t idx = _f.idx;
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? idx % UINT64_C(2) : idx) == UINT64_C(1)) {
          _stack.emplace_back(_after_sum_odd_indices_aux_in_true{a0});
        }
        _stack.emplace_back(_call{(idx + UINT64_C(1)), crane_raw(a1)});
      }
    } else {
      auto _f =
          std::move(std::get<_after_sum_odd_indices_aux_in_true>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices(const List<uint64_t> &l) {
  return sum_odd_indices_aux(l, UINT64_C(0));
}

uint64_t LoopifySpecialRecursion::categorize_by(uint64_t k,
                                                const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of categorize_by: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_categorize_by_in_false {};

  struct _after_categorize_by_in_true {};

  struct _after_categorize_by_in_true_2 {};

  using _frame = std::variant<_call, _after_categorize_by_in_false,
                              _after_categorize_by_in_true,
                              _after_categorize_by_in_true_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (k < a0) {
          _stack.emplace_back(_after_categorize_by_in_true{});
        } else if (a0 == k) {
          _stack.emplace_back(_after_categorize_by_in_true_2{});
        } else {
          _stack.emplace_back(_after_categorize_by_in_false{});
        }
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else if (std::holds_alternative<_after_categorize_by_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_categorize_by_in_false>(_popped));
      _stack.pop_back();
      _result = (UINT64_C(1) + _result);
    } else if (std::holds_alternative<_after_categorize_by_in_true>(_popped)) {
      auto _f = std::move(std::get<_after_categorize_by_in_true>(_popped));
      _stack.pop_back();
      _result = (UINT64_C(3) + _result);
    } else {
      auto _f = std::move(std::get<_after_categorize_by_in_true_2>(_popped));
      _stack.pop_back();
      _result = (UINT64_C(2) + _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifySpecialRecursion::between(uint64_t lo, uint64_t hi,
                                                const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (lo <= a0) {
        if (a0 <= hi) {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
          continue;
        }
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t>
LoopifySpecialRecursion::merge_levels(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of merge_levels: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_merge_levels_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_merge_levels_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_merge_levels_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_merge_levels_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(std::move(_result));
    }
  }
  return _result;
}
