#include "loopify_list_of_lists.h"

List<uint64_t> LoopifyListOfLists::intercalate(
    const List<uint64_t> &sep,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
    List<uint64_t> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0.app(_f.sep.app(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListOfLists::map_hd(const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = a1.get();
        continue;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(a0.v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a00, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_ll = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>>
LoopifyListOfLists::map_tl(const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = a1.get();
        continue;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(a0.v());
        auto _cell = std::make_unique<List<List<uint64_t>>>(
            typename List<List<uint64_t>>::Cons(*a10, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut())
                 .a1;
        _loop_ll = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

bool LoopifyListOfLists::all_empty(const List<List<uint64_t>> &ll) {
  bool _result;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = a1.get();
      } else {
        _result = false;
        break;
      }
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListOfLists::transpose_fuel(uint64_t fuel,
                                   const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<List<uint64_t>>> _head{};
  std::unique_ptr<List<List<uint64_t>>> *_write = &_head;
  List<List<uint64_t>> _loop_ll = ll;
  uint64_t _loop_fuel = std::move(fuel);
  while (true) {
    if (_loop_fuel <= 0) {
      *_write =
          std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_ll.v())) {
        *_write =
            std::make_unique<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_ll.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
          *_write = std::make_unique<List<List<uint64_t>>>(
              List<List<uint64_t>>::nil());
          break;
        } else {
          if (all_empty(_loop_ll)) {
            *_write = std::make_unique<List<List<uint64_t>>>(
                List<List<uint64_t>>::nil());
            break;
          } else {
            List<uint64_t> heads = map_hd(_loop_ll);
            List<List<uint64_t>> tails = map_tl(_loop_ll);
            auto _cell = std::make_unique<List<List<uint64_t>>>(
                typename List<List<uint64_t>>::Cons(std::move(heads), nullptr));
            *_write = std::move(_cell);
            _write = &std::get<typename List<List<uint64_t>>::Cons>(
                          (*_write)->v_mut())
                          .a1;
            _loop_ll = std::move(tails);
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyListOfLists::list_len(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(UINT64_C(1)) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified list_len: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{UINT64_C(1)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t LoopifyListOfLists::total_length(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(list_len(std::declval<List<uint64_t> &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified total_length: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{list_len(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListOfLists::transpose(const List<List<uint64_t>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

List<uint64_t> LoopifyListOfLists::flatten(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified flatten: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.a0.app(_result);
    }
  }
  return _result;
}

uint64_t LoopifyListOfLists::count_total(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(list_len(std::declval<List<uint64_t> &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified count_total: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{list_len(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListOfLists::firsts(const List<List<uint64_t>> &ll) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = a1.get();
        continue;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(a0.v());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a00, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_ll = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

bool LoopifyListOfLists::all_nil(const List<List<uint64_t>> &ll) {
  bool _result;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      _result = true;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = a1.get();
      } else {
        _result = false;
        break;
      }
    }
  }
  return _result;
}

List<std::pair<List<uint64_t>, List<uint64_t>>>
LoopifyListOfLists::zip_lists(const List<List<uint64_t>> &ll1,
                              const List<List<uint64_t>> &ll2) {
  std::unique_ptr<List<std::pair<List<uint64_t>, List<uint64_t>>>> _head{};
  std::unique_ptr<List<std::pair<List<uint64_t>, List<uint64_t>>>> *_write =
      &_head;
  const List<List<uint64_t>> *_loop_ll2 = &ll2;
  const List<List<uint64_t>> *_loop_ll1 = &ll1;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll1->v())) {
      *_write =
          std::make_unique<List<std::pair<List<uint64_t>, List<uint64_t>>>>(
              List<std::pair<List<uint64_t>, List<uint64_t>>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll1->v());
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_ll2->v())) {
        *_write =
            std::make_unique<List<std::pair<List<uint64_t>, List<uint64_t>>>>(
                List<std::pair<List<uint64_t>, List<uint64_t>>>::nil());
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_ll2->v());
        auto _cell =
            std::make_unique<List<std::pair<List<uint64_t>, List<uint64_t>>>>(
                typename List<std::pair<List<uint64_t>, List<uint64_t>>>::Cons(
                    std::make_pair(a0, a00), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<
            std::pair<List<uint64_t>, List<uint64_t>>>::Cons>(
                      (*_write)->v_mut())
                      .a1;
        _loop_ll2 = a10.get();
        _loop_ll1 = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyListOfLists::max_length(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(list_len(std::declval<List<uint64_t> &>())) a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified max_length: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{list_len(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = std::max(_f.a0, _result);
    }
  }
  return _result;
}
