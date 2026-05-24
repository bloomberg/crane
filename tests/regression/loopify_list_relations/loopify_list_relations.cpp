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
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s0;
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

List<uint64_t>
LoopifyListRelations::find_sublists_aux(const List<uint64_t> &needle,
                                        const List<uint64_t> &haystack,
                                        uint64_t idx) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_idx = std::move(idx);
  const List<uint64_t> *_loop_haystack = &haystack;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_haystack->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_haystack->v());
      if (is_prefix_of(needle, *_loop_haystack)) {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(_loop_idx, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_idx = (_loop_idx + UINT64_C(1));
        _loop_haystack = a1.get();
        continue;
      } else {
        _loop_idx = (_loop_idx + UINT64_C(1));
        _loop_haystack = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
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
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s0;
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

List<std::pair<uint64_t, uint64_t>>
LoopifyListRelations::zip(const List<uint64_t> &l1, const List<uint64_t> &l2) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
            List<std::pair<uint64_t, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
            typename List<std::pair<uint64_t, uint64_t>>::Cons(
                std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                      (*_write)->v_mut())
                      .l;
        _loop_l2 = a10.get();
        _loop_l1 = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
LoopifyListRelations::zip3(const List<uint64_t> &l1, const List<uint64_t> &l2,
                           const List<uint64_t> &l3) {
  std::shared_ptr<List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>
      _head{};
  std::shared_ptr<List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>
      *_write = &_head;
  const List<uint64_t> *_loop_l3 = &l3;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_shared<
          List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
          List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        *_write = std::make_shared<
            List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
            List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l3->v())) {
          *_write = std::make_shared<
              List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
              List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::nil());
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_loop_l3->v());
          auto _cell = std::make_shared<
              List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>>(
              typename List<
                  std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::
                  Cons(std::make_pair(std::make_pair(a0, a00), a01), nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_l3 = a11.get();
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListRelations::interleave(List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      *_write = std::make_shared<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        *_write = std::make_shared<List<uint64_t>>(_loop_l1);
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a0), nullptr));
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a00), nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).l =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .l->v_mut())
                 .l;
        _loop_l2 = std::move(*a10);
        _loop_l1 = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListRelations::merge_fuel(uint64_t fuel,
                                                List<uint64_t> l1,
                                                List<uint64_t> l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l1.v_mut())) {
        *_write = std::make_shared<List<uint64_t>>(std::move(_loop_l2));
        break;
      } else {
        auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_l2.v_mut())) {
          *_write = std::make_shared<List<uint64_t>>(_loop_l1);
          break;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
          if (a0 <= a00) {
            auto _cell = std::make_shared<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a0), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l1 = std::move(*a1);
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = std::make_shared<List<uint64_t>>(
                typename List<uint64_t>::Cons(std::move(a00), nullptr));
            *_write = std::move(_cell);
            _write =
                &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
            _loop_l2 = std::move(*a10);
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListRelations::merge(const List<uint64_t> &l1,
                                           const List<uint64_t> &l2) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  return merge_fuel((len1 + len2), l1, l2);
}

List<uint64_t> LoopifyListRelations::union_(const List<uint64_t> &l1,
                                            List<uint64_t> l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_shared<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
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
            return member(a0, _loop_l2);
          }()) {
        _loop_l1 = a1.get();
        continue;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l1 = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListRelations::intersection(const List<uint64_t> &l1,
                                                  const List<uint64_t> &l2) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
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
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l1 = a1.get();
        continue;
      } else {
        _loop_l1 = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}
