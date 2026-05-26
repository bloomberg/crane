#include "loopify_list_relations.h"

bool LoopifyListRelations::is_prefix_of(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified is_prefix_of: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = true;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{a0 == a00});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

bool LoopifyListRelations::is_suffix_of(const List<uint64_t> &l1,
                                        const List<uint64_t> &l2) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  if (len2 < len1) {
    return false;
  } else {
    uint64_t diff = (((len2 - len1) > len2 ? 0 : (len2 - len1)));
    List<uint64_t> suffix;
    auto drop_impl = [](auto &_self_drop, uint64_t n,
                        List<uint64_t> xs) -> List<uint64_t> {
      if (n <= 0) {
        return xs;
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v_mut())) {
          return List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v_mut());
          return _self_drop(_self_drop, n_, *a1);
        }
      }
    };
    auto drop = [&](uint64_t n, List<uint64_t> xs) -> List<uint64_t> {
      return drop_impl(drop_impl, n, xs);
    };
    suffix = drop(diff, l2);
    auto eq_impl = [](auto &_self_eq, const List<uint64_t> &a,
                      const List<uint64_t> &b) -> bool {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(b.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(a.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(b.v())) {
          return false;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(b.v());
          if (a00 == a01) {
            return _self_eq(_self_eq, *a10, *a11);
          } else {
            return false;
          }
        }
      }
    };
    auto eq = [&](const List<uint64_t> &a, const List<uint64_t> &b) -> bool {
      return eq_impl(eq_impl, a, b);
    };
    return eq(l1, suffix);
  }
}

bool LoopifyListRelations::is_infix_of_aux(const List<uint64_t> &needle,
                                           const List<uint64_t> &haystack) {
  const List<uint64_t> *_loop_haystack = &haystack;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_haystack->v())) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(needle.v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_haystack->v());
      if (is_prefix_of(needle, *_loop_haystack)) {
        return true;
      } else {
        _loop_haystack = a1.get();
      }
    }
  }
}

bool LoopifyListRelations::is_infix_of(const List<uint64_t> &_x0,
                                       const List<uint64_t> &_x1) {
  return is_infix_of_aux(_x0, _x1);
}

List<uint64_t> LoopifyListRelations::find_sublists_aux(
    const List<uint64_t> &needle, const List<uint64_t> &haystack,
    uint64_t
        idx) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t idx;
    const List<uint64_t> *haystack;
  };

  /// _Resume1: saves [idx], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t idx;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{idx, &haystack});
  /// Loopified find_sublists_aux: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t idx = _f.idx;
      const List<uint64_t> &haystack = *_f.haystack;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(haystack.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(haystack.v());
        if (is_prefix_of(needle, haystack)) {
          _stack.emplace_back(_Resume1{idx});
          _stack.emplace_back(_Enter{(idx + UINT64_C(1)), a1.get()});
        } else {
          _stack.emplace_back(_Enter{(idx + UINT64_C(1)), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.idx, _result);
    }
  }
  return _result;
}

List<uint64_t>
LoopifyListRelations::find_sublists(const List<uint64_t> &needle,
                                    const List<uint64_t> &haystack) {
  return find_sublists_aux(needle, haystack, UINT64_C(0));
}

bool LoopifyListRelations::list_eq(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::declval<uint64_t &>() ==
                          std::declval<uint64_t &>())>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified list_eq: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{a0 == a00});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

uint64_t LoopifyListRelations::list_compare(const List<uint64_t> &l1,
                                            const List<uint64_t> &l2) {
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return UINT64_C(0);
      } else {
        return UINT64_C(1);
      }
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return UINT64_C(2);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (a0 < a00) {
          return UINT64_C(1);
        } else {
          if (a00 < a0) {
            return UINT64_C(2);
          } else {
            _loop_l2 = a10.get();
            _loop_l1 = a1.get();
          }
        }
      }
    }
  }
}

List<std::pair<uint64_t, uint64_t>> LoopifyListRelations::zip(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2, &l1});
  /// Loopified zip: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result = List<std::pair<uint64_t, uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{std::make_pair(a0, a00)});
          _stack.emplace_back(_Enter{a10.get(), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, _result);
    }
  }
  return _result;
}

List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
LoopifyListRelations::zip3(
    const List<uint64_t> &l1, const List<uint64_t> &l2,
    const List<uint64_t>
        &l3) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l3;
    const List<uint64_t> *l2;
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(
        std::make_pair(std::declval<uint64_t &>(), std::declval<uint64_t &>()),
        std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l3, &l2, &l1});
  /// Loopified zip3: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l3 = *_f.l3;
      const List<uint64_t> &l2 = *_f.l2;
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result =
            List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
          _result =
              List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l3.v())) {
            _result =
                List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil();
          } else {
            const auto &[a01, a11] =
                std::get<typename List<uint64_t>::Cons>(l3.v());
            _stack.emplace_back(
                _Resume_Cons{std::make_pair(std::make_pair(a0, a00), a01)});
            _stack.emplace_back(_Enter{a11.get(), a10.get(), a1.get()});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::cons(
          _f._s0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListRelations::interleave(
    List<uint64_t> l1,
    List<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l2;
    List<uint64_t> l1;
  };

  /// _Resume_Cons: saves [a0, a00], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), std::move(l1)});
  /// Loopified interleave: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      List<uint64_t> l1 = std::move(_f.l1);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
        _result = std::move(l2);
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v_mut())) {
          _result = std::move(l1);
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v_mut());
          _stack.emplace_back(_Resume_Cons{std::move(a0), std::move(a00)});
          _stack.emplace_back(_Enter{*a10, *a1});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          List<uint64_t>::cons(_f.a0, List<uint64_t>::cons(_f.a00, _result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListRelations::merge_fuel(
    uint64_t fuel, List<uint64_t> l1,
    List<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l2;
    List<uint64_t> l1;
    uint64_t fuel;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  /// _Resume2: saves [a00], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), std::move(l1), fuel});
  /// Loopified merge_fuel: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      List<uint64_t> l1 = std::move(_f.l1);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
          _result = std::move(l2);
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  l2.v_mut())) {
            _result = std::move(l1);
          } else {
            auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(l2.v_mut());
            if (a0 <= a00) {
              _stack.emplace_back(_Resume1{std::move(a0)});
              _stack.emplace_back(_Enter{l2, *a1, fuel_});
            } else {
              _stack.emplace_back(_Resume2{std::move(a00)});
              _stack.emplace_back(_Enter{*a10, l1, fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = List<uint64_t>::cons(_f.a00, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListRelations::merge(const List<uint64_t> &l1,
                                           const List<uint64_t> &l2) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  return merge_fuel((len1 + len2), l1, l2);
}

List<uint64_t> LoopifyListRelations::union_(
    const List<uint64_t> &l1,
    List<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l2;
    const List<uint64_t> *l1;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), &l1});
  /// Loopified union: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = std::move(l2);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if ([&]() {
              auto member_impl = [](auto &_self_member, uint64_t y,
                                    const List<uint64_t> &ys) -> bool {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        ys.v())) {
                  return false;
                } else {
                  const auto &[a2, a3] =
                      std::get<typename List<uint64_t>::Cons>(ys.v());
                  return (y == a2 || _self_member(_self_member, y, *a3));
                }
              };
              auto member = [&](uint64_t y, const List<uint64_t> &ys) -> bool {
                return member_impl(member_impl, y, ys);
              };
              return member(a0, l2);
            }()) {
          _stack.emplace_back(_Enter{std::move(l2), a1.get()});
        } else {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{std::move(l2), a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListRelations::intersection(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l1;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l1});
  /// Loopified intersection: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        if ([&]() {
              auto member_impl = [](auto &_self_member, uint64_t y,
                                    const List<uint64_t> &ys) -> bool {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        ys.v())) {
                  return false;
                } else {
                  const auto &[a2, a3] =
                      std::get<typename List<uint64_t>::Cons>(ys.v());
                  return (y == a2 || _self_member(_self_member, y, *a3));
                }
              };
              auto member = [&](uint64_t y, const List<uint64_t> &ys) -> bool {
                return member_impl(member_impl, y, ys);
              };
              return member(a0, l2);
            }()) {
          _stack.emplace_back(_Resume1{a0});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
}
