#include "lent_alias_by_reference.h"

/// A lent parameter of a value inductive is passed by const reference
/// whether its type names the inductive or an abbreviation of it
/// (Translation_support.names_value_inductive); a frame machine holds one
/// so by pointer.
/// Read only: lent, by const reference.
uint64_t LentAliasByReference::bag_size(const LentAliasByReference::bag &x0_) {
  return x0_.length();
}

uint64_t
LentAliasByReference::big_bag_size(const LentAliasByReference::big_bag &x0_) {
  return x0_.length();
}

/// Not tail recursive: a frame machine, whose frames point at the cells of
/// the lent bag rather than copying them.
uint64_t LentAliasByReference::bag_sum(const List<uint64_t> &b) {
  // Explicit stack replaces the non-tail recursion of bag_sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *b;
  };

  struct _after_bag_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_bag_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&b});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &b = *_f.b;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(b.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(b.v());
        _stack.emplace_back(_after_bag_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_bag_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

/// Two lent abbreviation-typed parameters, walked in step.
uint64_t LentAliasByReference::dot(const List<uint64_t> &a,
                                   const List<uint64_t> &b) {
  // Explicit stack replaces the non-tail recursion of dot: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *b;
    const List<uint64_t> *a;
  };

  struct _after_dot_in_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _frame = std::variant<_call, _after_dot_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&b, &a});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &b = *_f.b;
      const List<uint64_t> &a = *_f.a;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(a.v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(b.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(b.v());
          _stack.emplace_back(_after_dot_in_Cons{a0, a00});
          _stack.emplace_back(_call{crane_raw(a10), crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_dot_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      _result = ((a0 * a00) + std::move(_result));
    }
  }
  return _result;
}

/// Kept whole: owned, by value, moved in.
LentAliasByReference::bag LentAliasByReference::push(uint64_t x,
                                                     const List<uint64_t> &b) {
  return List<uint64_t>::cons(x, b);
}
