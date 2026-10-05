#include "loopify_special_recursion.h"

List<uint64_t> LoopifySpecialRecursion::process_twice_fuel(
    uint64_t fuel,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, fuel_], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    uint64_t fuel_;
  };

  /// CraneCont_Cons_1: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons_1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{l, fuel});
  /// Loopified process_twice_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, fuel_});
          _stack.emplace_back(CraneEnter{*a1, fuel_});
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t fuel_ = _f.fuel_;
      List<uint64_t> first = std::move(_result);
      _stack.emplace_back(CraneCont_Cons_1{a0});
      _stack.emplace_back(CraneEnter{std::move(first), fuel_});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
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

List<uint64_t> LoopifySpecialRecursion::double_append(
    const List<uint64_t> &l1,
    List<uint64_t> l2) { /// CraneEnter: captures varying parameters for each
                         /// recursive call.

  struct CraneEnter {
    List<uint64_t> l2;
    const List<uint64_t> *l1;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l2), &l1});
  /// Loopified double_append: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{std::move(l2), crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = std::move(_result);
      _result = List<uint64_t>::cons(a0, rest.app(rest));
    }
  }
  return _result;
}

List<uint64_t>
LoopifySpecialRecursion::remove_if_sum_even(const List<uint64_t> &l) {
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
          const auto &[a00, a10] =
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
        auto _value = List<uint64_t>::cons(x, *_loop_l);
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifySpecialRecursion::collect_sorted(
    const LoopifySpecialRecursion::tree
        &t) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const LoopifySpecialRecursion::tree *t;
  };

  /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node {
    uint64_t a1;
    const LoopifySpecialRecursion::tree *a2;
  };

  /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Node_1 {
    List<uint64_t> _tmp2;
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&t});
  /// Loopified collect_sorted: CraneEnter -> CraneCont_Node ->
  /// CraneCont_Node_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifySpecialRecursion::tree &t = *_f.t;
      if (std::holds_alternative<typename LoopifySpecialRecursion::tree::Leaf>(
              t.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename LoopifySpecialRecursion::tree::Node>(t.v());
        _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Node>(_frame));
      uint64_t a1 = _f.a1;
      const LoopifySpecialRecursion::tree &a2 = *_f.a2;
      _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
      _stack.emplace_back(CraneEnter{&a2});
    } else {
      auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
      uint64_t a1 = _f.a1;
      _result =
          std::move(_f._tmp2).app(List<uint64_t>::cons(a1, std::move(_result)));
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices_aux(
    const List<uint64_t> &l,
    uint64_t idx) { /// CraneEnter: captures varying parameters for each
                    /// recursive call.

  struct CraneEnter {
    uint64_t idx;
    const List<uint64_t> *l;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{idx, &l});
  /// Loopified sum_odd_indices_aux: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t idx = _f.idx;
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? idx % UINT64_C(2) : idx) == UINT64_C(1)) {
          _stack.emplace_back(CraneCont1{a0});
          _stack.emplace_back(CraneEnter{(idx + UINT64_C(1)), crane_raw(a1)});
        } else {
          _stack.emplace_back(CraneEnter{(idx + UINT64_C(1)), crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifySpecialRecursion::sum_odd_indices(const List<uint64_t> &l) {
  return sum_odd_indices_aux(l, UINT64_C(0));
}

uint64_t LoopifySpecialRecursion::categorize_by(
    uint64_t k,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  /// CraneCont2: resumes after recursive call, then processes rest.
  struct CraneCont2 {};

  /// CraneCont3: resumes after recursive call, then processes rest.
  struct CraneCont3 {};

  using CraneFrame =
      std::variant<CraneEnter, CraneCont1, CraneCont2, CraneCont3>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified categorize_by: CraneEnter -> CraneCont1 -> CraneCont2 ->
  /// CraneCont3.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (k < a0) {
          _stack.emplace_back(CraneCont1{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          if (a0 == k) {
            _stack.emplace_back(CraneCont2{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          } else {
            _stack.emplace_back(CraneCont3{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = (UINT64_C(3) + std::move(_result));
    } else if (std::holds_alternative<CraneCont2>(_frame)) {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      _result = (UINT64_C(2) + std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont3>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifySpecialRecursion::between(uint64_t lo, uint64_t hi,
                                                const List<uint64_t> &l) {
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

List<uint64_t> LoopifySpecialRecursion::merge_levels(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified merge_levels: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(std::move(_result));
    }
  }
  return _result;
}
