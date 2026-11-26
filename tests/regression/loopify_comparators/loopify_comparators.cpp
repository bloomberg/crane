#include "loopify_comparators.h"

uint64_t LoopifyComparators::maximum_by(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of maximum_by: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_maximum_by_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_maximum_by_in_Cons>;
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
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_maximum_by_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_maximum_by_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t m = _result;
      if (m < a0) {
        _result = a0;
      } else {
        _result = m;
      }
    }
  }
  return _result;
}

uint64_t LoopifyComparators::minimum_by(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of minimum_by: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_minimum_by_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_minimum_by_in_Cons>;
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
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_after_minimum_by_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_minimum_by_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t m = _result;
      if (a0 < m) {
        _result = a0;
      } else {
        _result = m;
      }
    }
  }
  return _result;
}

List<uint64_t>
LoopifyComparators::merge_by_fuel(uint64_t fuel, const List<uint64_t> &l1,
                                  const List<uint64_t> &l2) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (fuel <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
        auto _value = *_loop_l2;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
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
          if (a0 <= a00) {
            auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l2 = &*_loop_l2;
            _loop_l1 = crane_raw(a1);
            fuel = fuel_;
            continue;
          } else {
            auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_l2 = crane_raw(a10);
            _loop_l1 = &*_loop_l1;
            fuel = fuel_;
            continue;
          }
        }
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyComparators::merge_by(const List<uint64_t> &l1,
                                            const List<uint64_t> &l2) {
  uint64_t len1 = l1.length();
  uint64_t len2 = l2.length();
  return merge_by_fuel((len1 + len2), l1, l2);
}

List<uint64_t> LoopifyComparators::insert_sorted(uint64_t x,
                                                 const List<uint64_t> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      auto _value = List<uint64_t>::cons(x, List<uint64_t>::nil());
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x <= a0) {
        auto _value = List<uint64_t>::cons(x, crane::shared_child(_loop_l));
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<uint64_t> LoopifyComparators::insertion_sort(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of insertion_sort: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_insertion_sort_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_insertion_sort_in_Cons>;
  List<uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_insertion_sort_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_insertion_sort_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = insert_sorted(a0, std::move(_result));
    }
  }
  return _result;
}

bool LoopifyComparators::is_sorted_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  List<uint64_t> _loop_l = l;
  while (true) {
    if (fuel <= 0) {
      return true;
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l.v())) {
        return true;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          return true;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          if (a0 <= a00) {
            _loop_l = List<uint64_t>::cons(a00, crane::shared_child(a10));
            fuel = fuel_;
          } else {
            return false;
          }
        }
      }
    }
  }
}

bool LoopifyComparators::is_sorted(const List<uint64_t> &l) {
  uint64_t len = l.length();
  return is_sorted_fuel(len, l);
}
