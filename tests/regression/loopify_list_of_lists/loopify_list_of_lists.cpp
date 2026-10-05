#include "loopify_list_of_lists.h"

List<uint64_t> LoopifyListOfLists::intercalate(
    const List<uint64_t> &sep,
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified intercalate: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = a0.app(sep.app(std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListOfLists::map_hd(const List<List<uint64_t>> &ll) {
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
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(a0.v());
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
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(a0.v());
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
  std::optional<List<List<uint64_t>>> _root{};
  std::shared_ptr<List<List<uint64_t>>> *_write = nullptr;
  List<List<uint64_t>> _loop_ll = ll;
  uint64_t _loop_fuel = fuel;
  while (true) {
    if (_loop_fuel <= 0) {
      auto _value = List<List<uint64_t>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<List<uint64_t>>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = _loop_fuel - 1;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_ll.v())) {
        auto _value = List<List<uint64_t>>::nil();
        (_write ? *(*_write = std::make_shared<List<List<uint64_t>>>(
                        std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
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
            _loop_fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyListOfLists::list_len(
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: resumes after recursive call, then processes rest.
  struct CraneCont_Cons {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified list_len: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyListOfLists::total_length(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified total_length: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = (list_len(a0) + std::move(_result));
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyListOfLists::transpose(const List<List<uint64_t>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

List<uint64_t> LoopifyListOfLists::flatten(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified flatten: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
        _write = &std::get<typename List<
            std::pair<List<uint64_t>, List<uint64_t>>>::Cons>(_node.v_mut())
                      .l;
        _loop_ll2 = crane_raw(a10);
        _loop_ll1 = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyListOfLists::max_length(
    const List<List<uint64_t>> &ll) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

  struct CraneEnter {
    const List<List<uint64_t>> *ll;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&ll});
  /// Loopified max_length: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = std::max(list_len(a0), std::move(_result));
    }
  }
  return _result;
}
