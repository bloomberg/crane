#include "loopify_list_of_lists.h"

List<uint64_t> LoopifyListOfLists::intercalate(const List<uint64_t> &sep,
                                               const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of intercalate: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_intercalate_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_intercalate_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_intercalate_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_intercalate_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(sep.app(std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListOfLists::map_hd(const List<List<uint64_t>> &ll) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = crane_raw(a1);
        continue;
      } else {
        const auto &[a00, _] = std::get<typename List<uint64_t>::Cons>(a0.v());
        auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_ll = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<List<uint64_t>>
LoopifyListOfLists::map_tl(const List<List<uint64_t>> &ll) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
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
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = crane_raw(a1);
        continue;
      } else {
        const auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(a0.v());
        auto _cell = typename List<List<uint64_t>>::Cons(*a10, nullptr);
        List<List<uint64_t>> &_node =
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
        _loop_ll = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

bool LoopifyListOfLists::all_empty(const List<List<uint64_t>> &ll) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<List<uint64_t>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
        _loop_ll = crane_raw(a1);
      } else {
        return false;
      }
    }
  }
}

List<List<uint64_t>>
LoopifyListOfLists::transpose_fuel(uint64_t fuel,
                                   const List<List<uint64_t>> &ll) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<List<uint64_t>> _loop_ll = ll;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_ll.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, _] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_ll.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(a0.v())) {
          auto _value = List<List<uint64_t>>::nil();
          (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                          std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          if (all_empty(_loop_ll)) {
            auto _value = List<List<uint64_t>>::nil();
            (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                            std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            List<uint64_t> heads = map_hd(_loop_ll);
            List<List<uint64_t>> tails = map_tl(_loop_ll);
            auto _cell =
                typename List<List<uint64_t>>::Cons(std::move(heads), nullptr);
            List<List<uint64_t>> &_node =
                (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write =
                &std::get<typename List<List<uint64_t>>::Cons>(_node.v_mut()).l;
            _loop_ll = std::move(tails);
            fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyListOfLists::list_len(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of list_len: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_list_len_in_Cons {};

  using _frame = std::variant<_call, _after_list_len_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_list_len_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_list_len_in_Cons>(_popped));
      _stack.pop_back();
      _result = UINT64_C(1) + _result;
    }
  }
  return _result;
}

uint64_t LoopifyListOfLists::total_length(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of total_length: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_total_length_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_total_length_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_total_length_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_total_length_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = list_len(std::move(a0)) + _result;
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListOfLists::transpose(const List<List<uint64_t>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

List<uint64_t> LoopifyListOfLists::flatten(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of flatten: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_flatten_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_flatten_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_flatten_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_flatten_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyListOfLists::count_total(const List<List<uint64_t>> &ll) {
  return total_length(ll);
}

List<uint64_t> LoopifyListOfLists::firsts(const List<List<uint64_t>> &ll) {
  return map_hd(ll);
}

bool LoopifyListOfLists::all_nil(const List<List<uint64_t>> &ll) {
  return all_empty(ll);
}

List<std::pair<List<uint64_t>, List<uint64_t>>>
LoopifyListOfLists::zip_lists(const List<List<uint64_t>> &ll1,
                              const List<List<uint64_t>> &ll2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<std::pair<List<uint64_t>, List<uint64_t>>>> _root{};
  std::shared_ptr<List<std::pair<List<uint64_t>, List<uint64_t>>>> *_write =
      nullptr;
  const List<List<uint64_t>> *_loop_ll2 = &ll2;
  const List<List<uint64_t>> *_loop_ll1 = &ll1;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_ll1->v())) {
      auto _value = List<std::pair<List<uint64_t>, List<uint64_t>>>::nil();
      (_write ? *(*_write = std::make_shared<
                      List<std::pair<List<uint64_t>, List<uint64_t>>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_ll1->v());
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_ll2->v())) {
        auto _value = List<std::pair<List<uint64_t>, List<uint64_t>>>::nil();
        (_write ? *(*_write = std::make_shared<
                        List<std::pair<List<uint64_t>, List<uint64_t>>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_ll2->v());
        auto _cell =
            typename List<std::pair<List<uint64_t>, List<uint64_t>>>::Cons(
                std::make_pair(a0, a00), nullptr);
        List<std::pair<List<uint64_t>, List<uint64_t>>> &_node =
            (_write ? *(*_write = std::make_shared<
                            List<std::pair<List<uint64_t>, List<uint64_t>>>>(
                            std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<
                typename List<std::pair<List<uint64_t>, List<uint64_t>>>::Cons>(
                _node.v_mut())
                .l;
        _loop_ll2 = crane_raw(a10);
        _loop_ll1 = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyListOfLists::max_length(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of max_length: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_max_length_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_max_length_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_max_length_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_max_length_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = std::max(list_len(std::move(a0)), _result);
    }
  }
  return _result;
}
