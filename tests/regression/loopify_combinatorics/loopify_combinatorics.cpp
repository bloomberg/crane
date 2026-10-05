#include "loopify_combinatorics.h"

/// Consolidated combinatorial algorithms.
/// remove x l removes first occurrence of x from list.
List<uint64_t> LoopifyCombinatorics::remove(uint64_t x,
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
      if (x == a0) {
        auto _value = *a1;
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
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

/// Helper: prepend x to each list in lsts.
List<List<uint64_t>>
LoopifyCombinatorics::map_cons(uint64_t x, const List<List<uint64_t>> &lsts) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = typename List<List<uint64_t>>::Cons(
          List<uint64_t>::cons(x, a0), nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_lsts = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function that handles both the choice
/// iteration and the recursive subproblem, enabling full loopification.
/// The match on remaining is hoisted out of the let-binding so that all
/// recursive calls appear at the top level of each branch.
List<List<uint64_t>> LoopifyCombinatorics::perms_choices_fuel(
    uint64_t fuel, const List<uint64_t> &choices,
    const List<uint64_t> &orig) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

  struct CraneEnter {
    List<uint64_t> orig;
    List<uint64_t> choices;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, a1, f, orig], resumes after recursive call,
  /// then processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    std::shared_ptr<List<uint64_t>> a1;
    uint64_t f;
    List<uint64_t> orig;
  };

  /// CraneCont_Cons_1: saves [_tmp3, a0], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    List<List<uint64_t>> _tmp3;
    uint64_t a0;
  };

  /// CraneCont_Nil: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Nil {
    uint64_t a0;
  };

  using CraneFrame =
      std::variant<CraneEnter, CraneCont_Cons, CraneCont_Cons_1, CraneCont_Nil>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{orig, choices, fuel});
  /// Loopified perms_choices_fuel: CraneEnter -> CraneCont_Cons ->
  /// CraneCont_Cons_1 -> CraneCont_Nil.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &orig = std::move(_f.orig);
      const List<uint64_t> &choices = std::move(_f.choices);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(choices.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(choices.v());
          List<uint64_t> remaining = remove(a0, orig);
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  remaining.v_mut())) {
            _stack.emplace_back(CraneCont_Nil{a0});
            _stack.emplace_back(CraneEnter{orig, *a1, f});
          } else {
            _stack.emplace_back(CraneCont_Cons{a0, a1, f, orig});
            _stack.emplace_back(CraneEnter{remaining, remaining, f});
          }
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      std::shared_ptr<List<uint64_t>> a1 = std::move(_f.a1);
      uint64_t f = _f.f;
      const List<uint64_t> &orig = std::move(_f.orig);
      _stack.emplace_back(CraneCont_Cons_1{std::move(_result), a0});
      _stack.emplace_back(CraneEnter{orig, *a1, f});
    } else if (std::holds_alternative<CraneCont_Cons_1>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      uint64_t a0 = _f.a0;
      _result = map_cons(a0, std::move(_f._tmp3)).app(std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont_Nil>(_frame));
      uint64_t a0 = _f.a0;
      _result =
          map_cons(a0, List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                                  List<List<uint64_t>>::nil()))
              .app(std::move(_result));
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of a list.
List<List<uint64_t>>
LoopifyCombinatorics::permutations_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                      List<List<uint64_t>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

uint64_t LoopifyCombinatorics::len_list(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified len_list: CraneEnter -> CraneCont_Cons.
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
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t LoopifyCombinatorics::factorial_impl(
    uint64_t n) { /// CraneEnter: captures varying parameters for each recursive
                  /// call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_m: saves [n], resumes after recursive call, then processes rest.
  struct CraneCont_m {
    uint64_t n;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_m>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified factorial_impl: CraneEnter -> CraneCont_m.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(CraneCont_m{n});
        _stack.emplace_back(CraneEnter{m});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_m>(_frame));
      uint64_t n = _f.n;
      _result = (n * std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyCombinatorics::permutations(const List<uint64_t> &l) {
  return permutations_fuel(factorial_impl(len_list(l)), l);
}

/// subsequences l generates all subsequences (subsets preserving order).
List<List<uint64_t>> LoopifyCombinatorics::subsequences(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified subsequences: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> rest = std::move(_result);
      auto map_prepend =
          [&](const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const List<List<uint64_t>> *lst;
        };
        /// CraneCont_Cons: saves [a0, a00], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Cons {
          std::decay_t<decltype(a0)> a0;
          List<uint64_t> a00;
        };
        using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
        List<List<uint64_t>> _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{&lst});
        /// Loopified map_prepend: CraneEnter -> CraneCont_Cons.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            const List<List<uint64_t>> &lst = *_f.lst;
            if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                    lst.v())) {
              _result = List<List<uint64_t>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<List<uint64_t>>::Cons>(lst.v());
              _stack.emplace_back(CraneCont_Cons{a0, a00});
              _stack.emplace_back(CraneEnter{crane_raw(a10)});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_Cons>(_frame));
            a0 = _f.a0;
            List<uint64_t> a00 = std::move(_f.a00);
            _result = List<List<uint64_t>>::cons(List<uint64_t>::cons(a0, a00),
                                                 std::move(_result));
          }
        }
        return _result;
      };
      _result = rest.app(map_prepend(rest));
    }
  }
  return _result;
}

/// Helper for cartesian product.
List<std::pair<uint64_t, uint64_t>>
LoopifyCombinatorics::map_pairs(uint64_t y, const List<uint64_t> &l) {
  std::optional<List<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
      (_write
           ? *(*_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                   std::move(_value)))
           : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
          std::make_pair(a0, y), nullptr);
      List<std::pair<uint64_t, uint64_t>> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                    _node.v_mut())
                    .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

/// cartesian l1 l2 Cartesian product of two lists.
List<std::pair<uint64_t, uint64_t>> LoopifyCombinatorics::cartesian(
    const List<uint64_t> &l1,
    const List<uint64_t> &l2) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l2;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l2});
  /// Loopified cartesian: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l2.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = map_pairs(a0, l1).app(std::move(_result));
    }
  }
  return _result;
}

/// power_set l generates the power set (all subsets).
List<List<uint64_t>> LoopifyCombinatorics::power_set(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified power_set: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> rest = std::move(_result);
      auto map_add_x =
          [&](const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const List<List<uint64_t>> *lst;
        };
        /// CraneCont_Cons: saves [a0, a00], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Cons {
          std::decay_t<decltype(a0)> a0;
          List<uint64_t> a00;
        };
        using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
        List<List<uint64_t>> _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{&lst});
        /// Loopified map_add_x: CraneEnter -> CraneCont_Cons.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            const List<List<uint64_t>> &lst = *_f.lst;
            if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                    lst.v())) {
              _result = List<List<uint64_t>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<List<uint64_t>>::Cons>(lst.v());
              _stack.emplace_back(CraneCont_Cons{a0, a00});
              _stack.emplace_back(CraneEnter{crane_raw(a10)});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_Cons>(_frame));
            a0 = _f.a0;
            List<uint64_t> a00 = std::move(_f.a00);
            _result = List<List<uint64_t>>::cons(List<uint64_t>::cons(a0, a00),
                                                 std::move(_result));
          }
        }
        return _result;
      };
      _result = rest.app(map_add_x(rest));
    }
  }
  return _result;
}

/// insert_everywhere x l inserts x at every position in l.
List<List<uint64_t>> LoopifyCombinatorics::insert_everywhere(
    uint64_t x,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0, l], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    uint64_t a0;
    List<uint64_t> l;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified insert_everywhere: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(x, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0, l});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const List<uint64_t> &l = std::move(_f.l);
      List<List<uint64_t>> rest = std::move(_result);
      auto prepend_y =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const List<List<uint64_t>> *lsts;
        };
        /// CraneCont_Cons: saves [a0, a00], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Cons {
          std::decay_t<decltype(a0)> a0;
          List<uint64_t> a00;
        };
        using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
        List<List<uint64_t>> _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{&lsts});
        /// Loopified prepend_y: CraneEnter -> CraneCont_Cons.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            const List<List<uint64_t>> &lsts = *_f.lsts;
            if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                    lsts.v())) {
              _result = List<List<uint64_t>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
              _stack.emplace_back(CraneCont_Cons{a0, a00});
              _stack.emplace_back(CraneEnter{crane_raw(a10)});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_Cons>(_frame));
            a0 = _f.a0;
            List<uint64_t> a00 = std::move(_f.a00);
            _result = List<List<uint64_t>>::cons(List<uint64_t>::cons(a0, a00),
                                                 std::move(_result));
          }
        }
        return _result;
      };
      _result = List<List<uint64_t>>::cons(List<uint64_t>::cons(x, l),
                                           prepend_y(std::move(rest)));
    }
  }
  return _result;
}

/// Helper: check if element is in list.
bool LoopifyCombinatorics::elem(
    uint64_t x,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  bool _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified elem: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = false;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = (x == a0 || std::move(_result));
    }
  }
  return _result;
}

/// Helper: list length.
uint64_t LoopifyCombinatorics::len_impl(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified len_impl: CraneEnter -> CraneCont_Cons.
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
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

/// dedup l removes all duplicates (keeps first occurrence).
List<uint64_t> LoopifyCombinatorics::dedup_fuel(
    uint64_t fuel,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, fuel});
  /// Loopified dedup_fuel: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1), f});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = std::move(_result);
      if (elem(a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<uint64_t>::cons(a0, std::move(rest));
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyCombinatorics::dedup(const List<uint64_t> &l) {
  return dedup_fuel(len_impl(l), l);
}
