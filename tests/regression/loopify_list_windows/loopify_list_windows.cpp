#include "loopify_list_windows.h"

uint64_t LoopifyListWindows::len(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + UINT64_C(1));
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

List<List<uint64_t>>
LoopifyListWindows::map_cons_helper(uint64_t x,
                                    const List<List<uint64_t>> &ll) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      auto _cell = typename List<List<uint64_t>>::Cons(
          List<uint64_t>::cons(x, a0), nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_ll = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListWindows::drop(uint64_t m, List<uint64_t> xs) {
  List<uint64_t> _loop_xs = std::move(xs);
  uint64_t _loop_m = std::move(m);
  while (true) {
    if (_loop_m <= 0) {
      return _loop_xs;
    } else {
      uint64_t m_ = _loop_m - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_xs.v_mut())) {
        return List<uint64_t>::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs.v_mut());
        _loop_xs = List<uint64_t>(*a1);
        _loop_m = m_;
      }
    }
  }
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListWindows::span_eq(
    uint64_t first,
    const List<uint64_t> &lst) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *lst;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&lst});
  /// Loopified span_eq: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &lst = *_f.lst;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(lst.v())) {
        _result = std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(lst.v());
        if (first == a0) {
          _stack.emplace_back(CraneCont1{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          _result = std::make_pair(List<uint64_t>::nil(), lst);
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a0 = _f.a0;
      auto [s, r] = std::move(_result);
      _result =
          std::make_pair(List<uint64_t>::cons(a0, std::move(s)), std::move(r));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListWindows::differences(const List<uint64_t> &l) {
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
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_sv1.v());
          auto _cell = typename List<uint64_t>::Cons(
              (((a01 - a0) > a01 ? 0 : (a01 - a0))), nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListWindows::sliding_pairs(const List<uint64_t> &l) {
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
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
        (_write ? *(*_write =
                        std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                            std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto &&_sv1 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
          auto _value = List<std::pair<uint64_t, uint64_t>>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_sv1.v());
          auto _cell = typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(a0, a01), nullptr);
          List<std::pair<uint64_t, uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<
                              List<std::pair<uint64_t, uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                   _node.v_mut())
                   .l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListWindows::inits(
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
  /// Loopified inits: CraneEnter -> CraneCont_Cons.
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
      _result = List<List<uint64_t>>::cons(
          List<uint64_t>::nil(), map_cons_helper(a0, std::move(_result)));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListWindows::tails(const List<uint64_t> &l) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                               List<List<uint64_t>>::nil());
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = typename List<List<uint64_t>>::Cons(*_loop_l, nullptr);
      List<List<uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListWindows::take(uint64_t n, const List<uint64_t> &l) {
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_n = n_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListWindows::windows_fuel(uint64_t fuel, uint64_t n,
                                                      const List<uint64_t> &l) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (len(*_loop_l) < n) {
          auto _value = List<List<uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell =
              typename List<List<uint64_t>>::Cons(take(n, *_loop_l), nullptr);
          List<List<uint64_t>> &_node =
              (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write =
              &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          _loop_fuel = fuel_;
          continue;
        }
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListWindows::windows(uint64_t n,
                                                 const List<uint64_t> &l) {
  return windows_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::chunks_fuel(uint64_t fuel, uint64_t n,
                                                     const List<uint64_t> &l) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        List<uint64_t> chunk = take(n, _loop_l);
        List<uint64_t> rest = drop(n, _loop_l);
        auto _cell =
            typename List<List<uint64_t>>::Cons(std::move(chunk), nullptr);
        List<List<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
        _loop_l = std::move(rest);
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListWindows::chunks(uint64_t n,
                                                const List<uint64_t> &l) {
  return chunks_fuel(len(l), n, l);
}

List<List<uint64_t>> LoopifyListWindows::group_fuel(uint64_t fuel,
                                                    const List<uint64_t> &l) {
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<uint64_t> _loop_l = l;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto [same, rest] = span_eq(a0, *a1);
        auto _cell = typename List<List<uint64_t>>::Cons(
            List<uint64_t>::cons(a0, std::move(same)), nullptr);
        List<List<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
        _loop_l = std::move(rest);
        _loop_fuel = fuel_;
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>> LoopifyListWindows::group(const List<uint64_t> &l) {
  return group_fuel(len(l), l);
}
