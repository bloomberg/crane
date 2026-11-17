#include "loopify_list_combining.h"

List<uint64_t> LoopifyListCombining::append(const List<uint64_t> &a,
                                            List<uint64_t> b) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_a = &a;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_a->v())) {
      auto _value = std::move(b);
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_a->v());
      auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_a = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyListCombining::intersperse(uint64_t sep,
                                                 const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        auto _value = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        auto _cell = typename List<uint64_t>::Cons(a0, std::move(_cell1));
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<uint64_t>::Cons>(std::get<
                typename List<uint64_t>::Cons>(_node.v_mut()).l->v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t>
LoopifyListCombining::intercalate(const List<uint64_t> &sep,
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
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
      List<uint64_t> a0 = std::move(_f.a0);
      _result = append(std::move(a0), append(sep, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::concat(const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of concat: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_concat_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_concat_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_after_concat_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_concat_in_Cons>(_popped));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = append(std::move(a0), std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::mapcat(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of mapcat: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_mapcat_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_mapcat_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_mapcat_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_mapcat_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      _result = append(List<uint64_t>::cons(
          a0, List<uint64_t>::cons(a0, List<uint64_t>::nil())),
                       std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::interleave_two(const List<uint64_t> &l1,
                                                    const List<uint64_t> &l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      auto _value = *_loop_l2;
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        auto _value = *_loop_l1;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        auto _cell1 = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a00, nullptr));
        auto _cell = typename List<uint64_t>::Cons(a0, std::move(_cell1));
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename List<uint64_t>::Cons>(std::get<
                typename List<uint64_t>::Cons>(_node.v_mut()).l->v_mut())
                .l;
        _loop_l2 = crane_raw(a10);
        _loop_l1 = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t>
LoopifyListCombining::concat_sep(uint64_t sep, const List<List<uint64_t>> &ll) {
  // Explicit stack replaces the non-tail recursion of concat_sep: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<List<uint64_t>> *ll;
  };

  struct _after_concat_sep_in_Cons {
    List<uint64_t> a0;
  };

  using _frame = std::variant<_call, _after_concat_sep_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ll});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
          _stack.emplace_back(_after_concat_sep_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_concat_sep_in_Cons>(_popped));
      List<uint64_t> a0 = std::move(_f.a0);
      _result =
          append(std::move(a0), List<uint64_t>::cons(sep, std::move(_result)));
    }
  }
  return _result;
}
