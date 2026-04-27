#include <loopify_list_relations.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) bool
LoopifyListRelations::is_prefix_of(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2) {
  struct _Enter {
    const List<unsigned int> l2;
    const List<unsigned int> l1;
  };

  struct _Call1 {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l2 = _f.l2;
      const List<unsigned int> l1 = _f.l1;
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
          _stack.emplace_back(_Call1{d_a0 == d_a00});
          _stack.emplace_back(_Enter{*(d_a10), *(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyListRelations::is_suffix_of(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  if (len2 < len1) {
    return false;
  } else {
    unsigned int diff = (((len2 - len1) > len2 ? 0 : (len2 - len1)));
    List<unsigned int> suffix;
    std::function<List<unsigned int>(unsigned int, List<unsigned int>)> drop;
    drop = [](unsigned int n, List<unsigned int> xs) -> List<unsigned int> {
      List<unsigned int> _result;
      List<unsigned int> _loop_xs = std::move(xs);
      unsigned int _loop_n = std::move(n);
      while (true) {
        if (_loop_n <= 0) {
          _result = _loop_xs;
          break;
        } else {
          unsigned int n_ = _loop_n - 1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_xs.v())) {
            _result = List<unsigned int>::nil();
            break;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename List<unsigned int>::Cons>(_loop_xs.v());
            List<unsigned int> _next_xs = *(d_a1);
            unsigned int _next_n = n_;
            _loop_xs = std::move(_next_xs);
            _loop_n = std::move(_next_n);
          }
        }
      }
      return _result;
    };
    suffix = drop(diff, l2);
    std::function<bool(List<unsigned int>, List<unsigned int>)> eq;
    eq = [](List<unsigned int> a, List<unsigned int> b) -> bool {
      bool _result;
      List<unsigned int> _loop_b = std::move(b);
      List<unsigned int> _loop_a = std::move(a);
      while (true) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_a.v())) {
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_b.v())) {
            _result = true;
            break;
          } else {
            _result = false;
            break;
          }
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_a.v());
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_b.v())) {
            _result = false;
            break;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename List<unsigned int>::Cons>(_loop_b.v());
            if (d_a00 == d_a01) {
              List<unsigned int> _next_b = *(d_a11);
              List<unsigned int> _next_a = *(d_a10);
              _loop_b = std::move(_next_b);
              _loop_a = std::move(_next_a);
            } else {
              _result = false;
              break;
            }
          }
        }
      }
      return _result;
    };
    return eq(l1, suffix);
  }
}

__attribute__((pure)) bool
LoopifyListRelations::is_infix_of_aux(const List<unsigned int> &needle,
                                      const List<unsigned int> &haystack) {
  bool _result;
  List<unsigned int> _loop_haystack = haystack;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_haystack.v())) {
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
          std::get<typename List<unsigned int>::Cons>(_loop_haystack.v());
      if (is_prefix_of(needle, _loop_haystack)) {
        _result = true;
        break;
      } else {
        _loop_haystack = *(d_a1);
      }
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyListRelations::is_infix_of(const List<unsigned int> &_x0,
                                  const List<unsigned int> &_x1) {
  return is_infix_of_aux(_x0, _x1);
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::find_sublists_aux(const List<unsigned int> &needle,
                                        const List<unsigned int> &haystack,
                                        unsigned int idx) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_idx = std::move(idx);
  List<unsigned int> _loop_haystack = haystack;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_haystack.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_haystack.v());
      if (is_prefix_of(needle, _loop_haystack)) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_idx, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        unsigned int _next_idx = (_loop_idx + 1u);
        List<unsigned int> _next_haystack = *(d_a1);
        _loop_idx = std::move(_next_idx);
        _loop_haystack = std::move(_next_haystack);
        continue;
      } else {
        unsigned int _next_idx = (_loop_idx + 1u);
        List<unsigned int> _next_haystack = *(d_a1);
        _loop_idx = std::move(_next_idx);
        _loop_haystack = std::move(_next_haystack);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::find_sublists(const List<unsigned int> &needle,
                                    const List<unsigned int> &haystack) {
  return find_sublists_aux(needle, haystack, 0u);
}

__attribute__((pure)) bool
LoopifyListRelations::list_eq(const List<unsigned int> &l1,
                              const List<unsigned int> &l2) {
  struct _Enter {
    const List<unsigned int> l2;
    const List<unsigned int> l1;
  };

  struct _Call1 {
    decltype(std::declval<unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l2 = _f.l2;
      const List<unsigned int> l1 = _f.l1;
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
          _stack.emplace_back(_Call1{d_a0 == d_a00});
          _stack.emplace_back(_Enter{*(d_a10), *(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 && _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListRelations::list_compare(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2) {
  unsigned int _result;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        _result = 0u;
        break;
      } else {
        _result = 1u;
        break;
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        _result = 2u;
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
        if (d_a0 < d_a00) {
          _result = 1u;
          break;
        } else {
          if (d_a00 < d_a0) {
            _result = 2u;
            break;
          } else {
            List<unsigned int> _next_l2 = *(d_a10);
            List<unsigned int> _next_l1 = *(d_a1);
            _loop_l2 = std::move(_next_l2);
            _loop_l1 = std::move(_next_l1);
          }
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListRelations::zip(const List<unsigned int> &l1,
                          const List<unsigned int> &l2) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
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
        List<unsigned int> _next_l2 = *(d_a10);
        List<unsigned int> _next_l1 = *(d_a1);
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure))
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
  List<unsigned int> _loop_l3 = l3;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<
          List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
          List<std::pair<std::pair<unsigned int, unsigned int>,
                         unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        *(_write) = std::make_unique<List<
            std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
            List<std::pair<std::pair<unsigned int, unsigned int>,
                           unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l3.v())) {
          *(_write) = std::make_unique<List<
              std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>(
              List<std::pair<std::pair<unsigned int, unsigned int>,
                             unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(_loop_l3.v());
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
          List<unsigned int> _next_l3 = *(d_a11);
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_l3 = std::move(_next_l3);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::interleave(List<unsigned int> l1, List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
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
        List<unsigned int> _next_l2 = *(d_a10);
        List<unsigned int> _next_l1 = *(d_a1);
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::merge_fuel(const unsigned int &fuel,
                                 List<unsigned int> l1, List<unsigned int> l2) {
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
              _loop_l1.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          if (d_a0 <= d_a00) {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l1 = *(d_a1);
            unsigned int _next_fuel = fuel_;
            _loop_l1 = std::move(_next_l1);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a00, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l2 = *(d_a10);
            unsigned int _next_fuel = fuel_;
            _loop_l2 = std::move(_next_l2);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::merge(const List<unsigned int> &l1,
                            const List<unsigned int> &l2) {
  unsigned int len1 = l1.length();
  unsigned int len2 = l2.length();
  return merge_fuel((len1 + len2), l1, l2);
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::union_(const List<unsigned int> &l1,
                             List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
      if ([&]() {
            std::function<bool(unsigned int, List<unsigned int>)> member;
            member = [&](unsigned int y, List<unsigned int> ys) -> bool {
              struct _Enter {
                List<unsigned int> ys;
              };
              struct _Call1 {
                decltype(std::declval<unsigned int &>() ==
                         std::declval<unsigned int &>()) _s0;
              };
              using _Frame = std::variant<_Enter, _Call1>;
              bool _result{};
              std::vector<_Frame> _stack;
              _stack.reserve(16);
              _stack.emplace_back(_Enter{ys});
              while (!_stack.empty()) {
                _Frame _frame = std::move(_stack.back());
                _stack.pop_back();
                if (std::holds_alternative<_Enter>(_frame)) {
                  auto _f = std::move(std::get<_Enter>(_frame));
                  List<unsigned int> ys = _f.ys;
                  if (std::holds_alternative<typename List<unsigned int>::Nil>(
                          ys.v())) {
                    _result = false;
                  } else {
                    const auto &[d_a0, d_a1] =
                        std::get<typename List<unsigned int>::Cons>(ys.v());
                    _stack.emplace_back(_Call1{y == d_a0});
                    _stack.emplace_back(_Enter{*(d_a1)});
                  }
                } else {
                  auto _f = std::move(std::get<_Call1>(_frame));
                  _result = (_f._s0 || _result);
                }
              }
              return _result;
            };
            return member(d_a0, l2);
          }()) {
        _loop_l1 = d_a1_value;
        continue;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l1 = d_a1_value;
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListRelations::intersection(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
      if ([&]() {
            std::function<bool(unsigned int, List<unsigned int>)> member;
            member = [&](unsigned int y, List<unsigned int> ys) -> bool {
              struct _Enter {
                List<unsigned int> ys;
              };
              struct _Call1 {
                decltype(std::declval<unsigned int &>() ==
                         std::declval<unsigned int &>()) _s0;
              };
              using _Frame = std::variant<_Enter, _Call1>;
              bool _result{};
              std::vector<_Frame> _stack;
              _stack.reserve(16);
              _stack.emplace_back(_Enter{ys});
              while (!_stack.empty()) {
                _Frame _frame = std::move(_stack.back());
                _stack.pop_back();
                if (std::holds_alternative<_Enter>(_frame)) {
                  auto _f = std::move(std::get<_Enter>(_frame));
                  List<unsigned int> ys = _f.ys;
                  if (std::holds_alternative<typename List<unsigned int>::Nil>(
                          ys.v())) {
                    _result = false;
                  } else {
                    const auto &[d_a0, d_a1] =
                        std::get<typename List<unsigned int>::Cons>(ys.v());
                    _stack.emplace_back(_Call1{y == d_a0});
                    _stack.emplace_back(_Enter{*(d_a1)});
                  }
                } else {
                  auto _f = std::move(std::get<_Call1>(_frame));
                  _result = (_f._s0 || _result);
                }
              }
              return _result;
            };
            return member(d_a0, l2);
          }()) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l1 = d_a1_value;
        continue;
      } else {
        _loop_l1 = d_a1_value;
        continue;
      }
    }
  }
  return std::move(*(_head));
}
