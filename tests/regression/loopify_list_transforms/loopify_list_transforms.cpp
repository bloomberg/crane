#include <loopify_list_transforms.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListTransforms::run_length_encode(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<std::pair<unsigned int, unsigned int>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto &&_sv = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
      return List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(d_a0, 1u),
          List<std::pair<unsigned int, unsigned int>>::nil());
    } else {
      auto &&_sv1 = run_length_encode(*(d_a1));
      if (std::holds_alternative<
              typename List<std::pair<unsigned int, unsigned int>>::Nil>(
              _sv1.v())) {
        return List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(d_a0, 1u),
            List<std::pair<unsigned int, unsigned int>>::nil());
      } else {
        const auto &[d_a01, d_a11] = std::get<
            typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _sv1.v());
        const unsigned int &y = d_a01.first;
        const unsigned int &n = d_a01.second;
        if (d_a0 == y) {
          return List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(y, (n + 1u)), *(d_a11));
        } else {
          return List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(d_a0, 1u),
              List<std::pair<unsigned int, unsigned int>>::cons(
                  std::make_pair(y, n), *(d_a11)));
        }
      }
    }
  }
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::prefix_sums(unsigned int acc,
                                   const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_acc, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_acc = (_loop_acc + d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListTransforms::sliding_pairs_fuel(const unsigned int &fuel,
                                          const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          *(_write) =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
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
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListTransforms::sliding_pairs(const List<unsigned int> &l) {
  unsigned int len = l.length();
  return sliding_pairs_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::abs_diff(const unsigned int &x, const unsigned int &y) {
  if (y < x) {
    return (((x - y) > x ? 0 : (x - y)));
  } else {
    return (((y - x) > y ? 0 : (y - x)));
  }
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::differences_fuel(const unsigned int &fuel,
                                        const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          *(_write) =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(abs_diff(d_a0, d_a00),
                                                nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          List<unsigned int> _next_l = *(d_a1);
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::differences(const List<unsigned int> &l) {
  unsigned int len = l.length();
  return differences_fuel(len, l);
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::take(const unsigned int &n,
                            const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n = n_;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::drop(const unsigned int &n, List<unsigned int> l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      _result = _loop_l;
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        List<unsigned int> _next_l = *(d_a1);
        unsigned int _next_n = n_;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListTransforms::chunks_of_fuel(const unsigned int &fuel,
                                      const unsigned int &n,
                                      const List<unsigned int> &l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (n <= 0u) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v())) {
          *(_write) = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          auto _cell = std::make_unique<List<List<unsigned int>>>(
              typename List<List<unsigned int>>::Cons(take(n, _loop_l),
                                                      nullptr));
          *(_write) = std::move(_cell);
          _write = &std::get<typename List<List<unsigned int>>::Cons>(
                        (*_write)->v_mut())
                        .d_a1;
          List<unsigned int> _next_l = drop(n, _loop_l);
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListTransforms::chunks_of(const unsigned int &n,
                                 const List<unsigned int> &l) {
  unsigned int len = l.length();
  return chunks_of_fuel(len, n, l);
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::rotate_left_fuel(const unsigned int &fuel,
                                        const unsigned int &n,
                                        List<unsigned int> l) {
  List<unsigned int> _result;
  List<unsigned int> _loop_l = std::move(l);
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      _result = _loop_l;
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        _result = _loop_l;
        break;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l.v())) {
          _result = List<unsigned int>::nil();
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l.v());
          List<unsigned int> rotated = (*(d_a1)).app(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
          List<unsigned int> _next_l = rotated;
          unsigned int _next_n =
              (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_n = std::move(_next_n);
          _loop_fuel = std::move(_next_fuel);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::rotate_left(const unsigned int &n,
                                   const List<unsigned int> &l) {
  return rotate_left_fuel((n + 1u), n, l);
}

__attribute__((pure)) List<unsigned int>
LoopifyListTransforms::uniq_sorted_fuel(const unsigned int &fuel,
                                        const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          if (d_a0 == d_a00) {
            List<unsigned int> _next_l = *(d_a1);
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = std::make_unique<List<unsigned int>>(
                typename List<unsigned int>::Cons(d_a0, nullptr));
            *(_write) = std::move(_cell);
            _write =
                &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1;
            List<unsigned int> _next_l = *(d_a1);
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
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
LoopifyListTransforms::uniq_sorted(const List<unsigned int> &l) {
  unsigned int len = l.length();
  return uniq_sorted_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::step_sum(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        unsigned int contribution;
        if ((2u ? d_a0 % 2u : d_a0) == 0u) {
          contribution = d_a0;
        } else {
          contribution = (d_a0 * 2u);
        }
        _stack.emplace_back(_Call1{contribution});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
