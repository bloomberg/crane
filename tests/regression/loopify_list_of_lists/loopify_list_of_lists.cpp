#include <loopify_list_of_lists.h>

__attribute__((pure)) List<unsigned int>
LoopifyListOfLists::intercalate(const List<unsigned int> &sep,
                                const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    const List<unsigned int> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                _sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_f._s1.app(_result));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListOfLists::map_hd(const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a0.v())) {
        _loop_ll = *(d_a1);
        continue;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a00, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_ll = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListOfLists::map_tl(const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a0.v())) {
        _loop_ll = *(d_a1);
        continue;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a0.v());
        auto _cell = std::make_unique<List<List<unsigned int>>>(
            typename List<List<unsigned int>>::Cons(*(d_a10), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<List<unsigned int>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        _loop_ll = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) bool
LoopifyListOfLists::all_empty(const List<List<unsigned int>> &ll) {
  bool _result;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a0.v())) {
        _loop_ll = *(d_a1);
      } else {
        _result = false;
        break;
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListOfLists::transpose_fuel(const unsigned int &fuel,
                                   const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<List<unsigned int>> _loop_ll = ll;
  unsigned int _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              _loop_ll.v())) {
        *(_write) = std::make_unique<List<List<unsigned int>>>(
            List<List<unsigned int>>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a0.v())) {
          *(_write) = std::make_unique<List<List<unsigned int>>>(
              List<List<unsigned int>>::nil());
          break;
        } else {
          if (all_empty(_loop_ll)) {
            *(_write) = std::make_unique<List<List<unsigned int>>>(
                List<List<unsigned int>>::nil());
            break;
          } else {
            List<unsigned int> heads = map_hd(_loop_ll);
            List<List<unsigned int>> tails = map_tl(_loop_ll);
            auto _cell = std::make_unique<List<List<unsigned int>>>(
                typename List<List<unsigned int>>::Cons(std::move(heads),
                                                        nullptr));
            *(_write) = std::move(_cell);
            _write = &std::get<typename List<List<unsigned int>>::Cons>(
                          (*_write)->v_mut())
                          .d_a1;
            List<List<unsigned int>> _next_ll = std::move(tails);
            unsigned int _next_fuel = fuel_;
            _loop_ll = std::move(_next_ll);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) unsigned int
LoopifyListOfLists::list_len(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
        _stack.emplace_back(_Call1{1u});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListOfLists::total_length(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    decltype(list_len(std::declval<List<unsigned int> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{list_len(d_a0)});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyListOfLists::transpose(const List<List<unsigned int>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

__attribute__((pure)) List<unsigned int>
LoopifyListOfLists::flatten(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListOfLists::count_total(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    decltype(list_len(std::declval<List<unsigned int> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{list_len(d_a0)});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListOfLists::firsts(const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a0.v())) {
        _loop_ll = *(d_a1);
        continue;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(d_a0.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a00, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_ll = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) bool
LoopifyListOfLists::all_nil(const List<List<unsigned int>> &ll) {
  bool _result;
  List<List<unsigned int>> _loop_ll = ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll.v())) {
      _result = true;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a0.v())) {
        _loop_ll = *(d_a1);
      } else {
        _result = false;
        break;
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<std::pair<List<unsigned int>, List<unsigned int>>>
LoopifyListOfLists::zip_lists(const List<List<unsigned int>> &ll1,
                              const List<List<unsigned int>> &ll2) {
  std::unique_ptr<List<std::pair<List<unsigned int>, List<unsigned int>>>>
      _head{};
  std::unique_ptr<List<std::pair<List<unsigned int>, List<unsigned int>>>>
      *_write = &_head;
  List<List<unsigned int>> _loop_ll2 = ll2;
  List<List<unsigned int>> _loop_ll1 = ll1;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll1.v())) {
      *(_write) = std::make_unique<
          List<std::pair<List<unsigned int>, List<unsigned int>>>>(
          List<std::pair<List<unsigned int>, List<unsigned int>>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll1.v());
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              _loop_ll2.v())) {
        *(_write) = std::make_unique<
            List<std::pair<List<unsigned int>, List<unsigned int>>>>(
            List<std::pair<List<unsigned int>, List<unsigned int>>>::nil());
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<List<unsigned int>>::Cons>(_loop_ll2.v());
        auto _cell = std::make_unique<
            List<std::pair<List<unsigned int>, List<unsigned int>>>>(
            typename List<std::pair<List<unsigned int>, List<unsigned int>>>::
                Cons(std::make_pair(d_a0, d_a00), nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<
            std::pair<List<unsigned int>, List<unsigned int>>>::Cons>(
                      (*_write)->v_mut())
                      .d_a1;
        List<List<unsigned int>> _next_ll2 = *(d_a10);
        List<List<unsigned int>> _next_ll1 = *(d_a1);
        _loop_ll2 = std::move(_next_ll2);
        _loop_ll1 = std::move(_next_ll1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) unsigned int
LoopifyListOfLists::max_length(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    decltype(list_len(std::declval<List<unsigned int> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{list_len(d_a0)});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = std::max(_f._s0, _result);
    }
  }
  return _result;
}
