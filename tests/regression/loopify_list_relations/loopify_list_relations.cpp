#include "loopify_list_relations.h"

bool LoopifyListRelations::is_prefix_of(
    const List<unsigned int> &l1,
    const List<unsigned int>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l2;
    const List<unsigned int> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
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
      const List<unsigned int> &l2 = *(_f.l2);
      const List<unsigned int> &l1 = *(_f.l1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        _result = true;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{d_a0 == d_a00});
          _stack.emplace_back(_Enter{d_a10.get(), d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

bool LoopifyListRelations::is_suffix_of(const List<unsigned int> &l1,
                                        const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  if (len2 < len1) {
    return false;
  } else {
    unsigned int diff = (((len2 - len1) > len2 ? 0 : (len2 - len1)));
    List<unsigned int> suffix;
    auto drop_impl = [](auto &_self_drop, const unsigned int n,
                        List<unsigned int> xs) -> List<unsigned int> {
      if (n <= 0) {
        return xs;
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                xs.v_mut())) {
          return List<unsigned int>::nil();
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(xs.v_mut());
          return _self_drop(_self_drop, n_, *(d_a1));
        }
      }
    };
    auto drop = [&](const unsigned int n,
                    List<unsigned int> xs) -> List<unsigned int> {
      return drop_impl(drop_impl, n, xs);
    };
    suffix = drop(diff, l2);
    auto eq_impl = [](auto &_self_eq, const List<unsigned int> &a,
                      const List<unsigned int> &b) -> bool {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(a.v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(b.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(a.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(b.v())) {
          return false;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(b.v());
          if (d_a00 == d_a01) {
            return _self_eq(_self_eq, *(d_a10), *(d_a11));
          } else {
            return false;
          }
        }
      }
    };
    auto eq = [&](const List<unsigned int> &a,
                  const List<unsigned int> &b) -> bool {
      return eq_impl(eq_impl, a, b);
    };
    return eq(l1, suffix);
  }
}

bool LoopifyListRelations::is_infix_of_aux(const List<unsigned int> &needle,
                                           const List<unsigned int> &haystack) {
  bool _result;
  const List<unsigned int> *_loop_haystack = &haystack;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_haystack->v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              needle.v())) {
        _result = true;
        break;
      } else {
        _result = false;
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_haystack->v());
      if (is_prefix_of(needle, *(_loop_haystack))) {
        _result = true;
        break;
      } else {
        _loop_haystack = d_a1.get();
      }
    }
  }
  return _result;
}

bool LoopifyListRelations::is_infix_of(const List<unsigned int> &_x0,
                                       const List<unsigned int> &_x1) {
  return is_infix_of_aux(_x0, _x1);
}

List<unsigned int>
LoopifyListRelations::find_sublists_aux(const List<unsigned int> &needle,
                                        const List<unsigned int> &haystack,
                                        const unsigned int idx) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_idx = idx;
  const List<unsigned int> *_loop_haystack = &haystack;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_haystack->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_haystack->v());
      if (is_prefix_of(needle, *(_loop_haystack))) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_idx, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_idx = (_loop_idx + 1u);
        _loop_haystack = d_a1.get();
        continue;
      } else {
        _loop_idx = (_loop_idx + 1u);
        _loop_haystack = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int>
LoopifyListRelations::find_sublists(const List<unsigned int> &needle,
                                    const List<unsigned int> &haystack) {
  return find_sublists_aux(needle, haystack, 0u);
}

bool LoopifyListRelations::list_eq(
    const List<unsigned int> &l1,
    const List<unsigned int>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l2;
    const List<unsigned int> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
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
      const List<unsigned int> &l2 = *(_f.l2);
      const List<unsigned int> &l1 = *(_f.l1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1.v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          _result = true;
        } else {
          _result = false;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
          _result = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v());
          _stack.emplace_back(_Resume_Cons{d_a0 == d_a00});
          _stack.emplace_back(_Enter{d_a10.get(), d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

unsigned int LoopifyListRelations::list_compare(const List<unsigned int> &l1,
                                                const List<unsigned int> &l2) {
  unsigned int _result;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 0u;
        break;
      } else {
        _result = 1u;
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = 2u;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        if (d_a0 < d_a00) {
          _result = 1u;
          break;
        } else {
          if (d_a00 < d_a0) {
            _result = 2u;
            break;
          } else {
            _loop_l2 = d_a10.get();
            _loop_l1 = d_a1.get();
          }
        }
      }
    }
  }
  return _result;
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListRelations::zip(const List<unsigned int> &l1,
                          const List<unsigned int> &l2) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        auto _cell =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                typename List<std::pair<unsigned int, unsigned int>>::Cons(
                    std::make_pair(d_a0, d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<
                 typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                 (*_write)->v_mut())
                 .d_a1;
        _loop_l2 = d_a10.get();
        _loop_l1 = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
LoopifyListRelations::zip3(const List<unsigned int> &l1,
                           const List<unsigned int> &l2,
                           const List<unsigned int> &l3) {
  std::unique_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _head{};
  std::unique_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      *_write = &_head;
  const List<unsigned int> *_loop_l3 = &l3;
  const List<unsigned int> *_loop_l2 = &l2;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) = std::make_unique<
          List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
          List<std::pair<std::pair<unsigned int, unsigned int>,
                         unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        *(_write) = std::make_unique<List<
            std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
            List<std::pair<std::pair<unsigned int, unsigned int>,
                           unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l3->v())) {
          *(_write) = std::make_unique<List<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              List<std::pair<std::pair<unsigned int, unsigned int>,
                             unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(_loop_l3->v());
          auto _cell = std::make_unique<List<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              typename List<std::pair<std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::
                  Cons(std::make_pair(std::make_pair(d_a0, d_a00), d_a01),
                       nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          _loop_l3 = d_a11.get();
          _loop_l2 = d_a10.get();
          _loop_l1 = d_a1.get();
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListRelations::interleave(List<unsigned int> l1,
                                                    List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v_mut())) {
      *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v_mut())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
        break;
      } else {
        auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v_mut());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a00, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_l2 = std::move(*(d_a10));
        _loop_l1 = std::move(*(d_a1));
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListRelations::merge_fuel(const unsigned int fuel,
                                                    List<unsigned int> l1,
                                                    List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v_mut())) {
        *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
        break;
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v_mut());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v_mut())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v_mut());
          if (d_a0 <= d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            _loop_l1 = std::move(*(d_a1));
            _loop_fuel = fuel_;
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a00, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            _loop_l2 = std::move(*(d_a10));
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int> LoopifyListRelations::merge(const List<unsigned int> &l1,
                                               const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  return merge_fuel((len1 + len2), l1, l2);
}

List<unsigned int> LoopifyListRelations::union_(const List<unsigned int> &l1,
                                                List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) = std::make_unique<List<unsigned int>>(std::move(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if ([&]() {
            auto member_impl = [](auto &_self_member, const unsigned int y,
                                  const List<unsigned int> &ys) -> bool {
              if (std::holds_alternative<typename List<unsigned int>::Nil>(
                      ys.v())) {
                return false;
              } else {
                const auto &[d_a0, d_a1] =
                    std::get<typename List<unsigned int>::Cons>(ys.v());
                return (y == d_a0 || _self_member(_self_member, y, *(d_a1)));
              }
            };
            auto member = [&](const unsigned int y,
                              const List<unsigned int> &ys) -> bool {
              return member_impl(member_impl, y, ys);
            };
            return member(d_a0, _loop_l2);
          }()) {
        _loop_l1 = d_a1.get();
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l1 = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

List<unsigned int>
LoopifyListRelations::intersection(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if ([&]() {
            auto member_impl = [](auto &_self_member, const unsigned int y,
                                  const List<unsigned int> &ys) -> bool {
              if (std::holds_alternative<typename List<unsigned int>::Nil>(
                      ys.v())) {
                return false;
              } else {
                const auto &[d_a0, d_a1] =
                    std::get<typename List<unsigned int>::Cons>(ys.v());
                return (y == d_a0 || _self_member(_self_member, y, *(d_a1)));
              }
            };
            auto member = [&](const unsigned int y,
                              const List<unsigned int> &ys) -> bool {
              return member_impl(member_impl, y, ys);
            };
            return member(d_a0, l2);
          }()) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l1 = d_a1.get();
        continue;
      } else {
        _loop_l1 = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}
