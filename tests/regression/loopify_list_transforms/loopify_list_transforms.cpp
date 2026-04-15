#include <loopify_list_transforms.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::run_length_encode(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  using _Frame = std::variant<_Enter>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    const auto &_f = std::get<_Enter>(_frame);
    const std::shared_ptr<List<unsigned int>> l = _f.l;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      _result = List<std::pair<unsigned int, unsigned int>>::nil();
    } else {
      const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
        _result = List<std::pair<unsigned int, unsigned int>>::cons(
            std::make_pair(_m.d_a0, 1u),
            List<std::pair<unsigned int, unsigned int>>::nil());
      } else {
        auto &&_sv1 = run_length_encode(_m.d_a1);
        if (std::holds_alternative<
                typename List<std::pair<unsigned int, unsigned int>>::Nil>(
                _sv1->v())) {
          _result = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(_m.d_a0, 1u),
              List<std::pair<unsigned int, unsigned int>>::nil());
        } else {
          const auto &_m1 = *std::get_if<
              typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              &_sv1->v());
          const unsigned int &y = _m1.d_a0.first;
          const unsigned int &n = _m1.d_a0.second;
          if (_m.d_a0 == y) {
            _result = List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(y, (n + 1u)), _m1.d_a1);
          } else {
            _result = List<std::pair<unsigned int, unsigned int>>::cons(
                std::make_pair(_m.d_a0, 1u),
                List<std::pair<unsigned int, unsigned int>>::cons(
                    std::make_pair(y, n), _m1.d_a1));
          }
        }
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::prefix_sums(
    const unsigned int acc, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(_loop_acc, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
      unsigned int _next_acc = (_loop_acc + _m.d_a0);
      _loop_l = std::move(_next_l);
      _loop_acc = std::move(_next_acc);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = List<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
        } else {
          _head = List<std::pair<unsigned int, unsigned int>>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0->v())) {
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
          } else {
            _head = List<std::pair<unsigned int, unsigned int>>::nil();
          }
          _continue = false;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(_m.d_a0, _m0.d_a0), nullptr);
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return sliding_pairs_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::abs_diff(const unsigned int x, const unsigned int y) {
  if (y < x) {
    return (((x - y) > x ? 0 : (x - y)));
  } else {
    return (((y - x) > y ? 0 : (y - x)));
  }
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::differences_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
          auto _cell =
              List<unsigned int>::cons(abs_diff(_m.d_a0, _m0.d_a0), nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::differences(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return differences_fuel(len, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::take(const unsigned int n,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_n = n_;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::drop(const unsigned int n,
                            std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_l);
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v()) &&
          _loop_l.use_count() == 1) {
        _result = _loop_l;
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l->v())) {
        _result = List<unsigned int>::nil();
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_n = n_;
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of_fuel(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (n <= 0u) {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l->v())) {
          if (_last) {
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                _last->v_mut())
                .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
          } else {
            _head = List<std::shared_ptr<List<unsigned int>>>::nil();
          }
          _continue = false;
        } else {
          auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
              take(n, _loop_l), nullptr);
          if (_last) {
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          std::shared_ptr<List<unsigned int>> _next_l = drop(n, _loop_l);
          unsigned int _next_fuel = fuel_;
          _loop_l = std::move(_next_l);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of(const unsigned int n,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return chunks_of_fuel(len, n, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::rotate_left_fuel(const unsigned int fuel,
                                        const unsigned int n,
                                        std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      _result = std::move(_loop_l);
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        _result = std::move(_loop_l);
        _continue = false;
      } else {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l->v()) &&
            _loop_l.use_count() == 1) {
          _result = _loop_l;
          _continue = false;
        } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                       _loop_l->v())) {
          _result = List<unsigned int>::nil();
          _continue = false;
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
          std::shared_ptr<List<unsigned int>> rotated = _m.d_a1->app(
              List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()));
          std::shared_ptr<List<unsigned int>> _next_l = std::move(rotated);
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

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::rotate_left(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  return rotate_left_fuel((n + 1u), n, l);
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
          } else {
            _head =
                List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil());
          }
          _continue = false;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
          if (_m.d_a0 == _m0.d_a0) {
            std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
            unsigned int _next_fuel = fuel_;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return uniq_sorted_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::step_sum(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        unsigned int contribution;
        if ((2u ? _m.d_a0 % 2u : _m.d_a0) == 0u) {
          contribution = _m.d_a0;
        } else {
          contribution = (_m.d_a0 * 2u);
        }
        _stack.emplace_back(_Call1{contribution});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}
