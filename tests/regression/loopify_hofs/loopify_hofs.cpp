#include "loopify_hofs.h"

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyHofs::is_prefix_of(const List<uint64_t> &l1,
                               const List<uint64_t> &l2) {
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = crane_raw(a10);
          _loop_l1 = crane_raw(a1);
        } else {
          return false;
        }
      }
    }
  }
}

/// lookup_all key l finds all values associated with key in association list.
List<uint64_t>
LoopifyHofs::lookup_all(uint64_t key,
                        const List<std::pair<uint64_t, uint64_t>> &l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        auto _cell = typename List<uint64_t>::Cons(v, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// Helper: get head of list with default.
uint64_t LoopifyHofs::head_default(uint64_t default0, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
List<List<uint64_t>> LoopifyHofs::subsequences(
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
      auto map_cons_x =
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
        /// Loopified map_cons_x: CraneEnter -> CraneCont_Cons.
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
      _result = rest.app(map_cons_x(rest));
    }
  }
  return _result;
}

/// Helper: pair element with all elements in list.
List<std::pair<uint64_t, uint64_t>>
LoopifyHofs::pair_with_all(uint64_t x, const List<uint64_t> &l) {
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
          std::make_pair(x, a0), nullptr);
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

/// cartesian l1 l2 computes cartesian product of two lists.
List<std::pair<uint64_t, uint64_t>> LoopifyHofs::cartesian(
    const List<uint64_t> &l1,
    const List<uint64_t> &l2) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l1;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l1});
  /// Loopified cartesian: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      _result = pair_with_all(a0, l2).app(std::move(_result));
    }
  }
  return _result;
}

/// longest_run l finds the longest consecutive run of equal elements.
/// Matches on recursive result to decide behavior.
List<uint64_t> LoopifyHofs::longest_run_fuel(
    uint64_t fuel, List<uint64_t> l) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

  struct CraneEnter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  /// CraneCont2: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont2 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified longest_run_fuel: CraneEnter -> CraneCont1 -> CraneCont2.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            _result =
                List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            if (a0 == a00) {
              _stack.emplace_back(CraneCont1{a0});
              _stack.emplace_back(
                  CraneEnter{List<uint64_t>::cons(a00, *a10), f});
            } else {
              _stack.emplace_back(CraneCont2{a0});
              _stack.emplace_back(
                  CraneEnter{List<uint64_t>::cons(a00, *a10), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<CraneCont1>(_frame)) {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a0 = _f.a0;
      _result = List<uint64_t>::cons(std::move(a0), std::move(_result));
    } else {
      auto _f = std::move(std::get<CraneCont2>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rec_result = std::move(_result);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              rec_result.v_mut())) {
        _result = List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
      } else {
        auto &[a01, a11] =
            std::get<typename List<uint64_t>::Cons>(rec_result.v_mut());
        if (std::move(a0) == a01) {
          _result = std::move(rec_result);
        } else {
          _result = std::move(rec_result);
        }
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyHofs::longest_run(const List<uint64_t> &l) {
  return longest_run_fuel(l.length(), l);
}

/// power_set l generates all subsets.
List<List<uint64_t>> LoopifyHofs::power_set(
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
      List<List<uint64_t>> sub = std::move(_result);
      auto map_cons_x =
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
        /// Loopified map_cons_x: CraneEnter -> CraneCont_Cons.
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
      _result = sub.app(map_cons_x(sub));
    }
  }
  return _result;
}
