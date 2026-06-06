#include "loopify_option_maybe.h"

std::optional<uint64_t> LoopifyOptionMaybe::find_even(const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        return std::make_optional<uint64_t>(a0);
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

std::optional<uint64_t>
LoopifyOptionMaybe::find_greater(uint64_t threshold, const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (threshold < a0) {
        return std::make_optional<uint64_t>(a0);
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

std::optional<uint64_t>
LoopifyOptionMaybe::lookup(uint64_t key,
                           const List<std::pair<uint64_t, uint64_t>> &l) {
  const List<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _loop_l->v());
      const uint64_t &k = a0.first;
      const uint64_t &v = a0.second;
      if (key == k) {
        return std::make_optional<uint64_t>(v);
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

List<uint64_t> LoopifyOptionMaybe::lookup_all(
    uint64_t key,
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume1: saves [v], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t v;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified lookup_all: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const uint64_t &k = a0.first;
        const uint64_t &v = a0.second;
        if (key == k) {
          _stack.emplace_back(_Resume1{v});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.v, std::move(_result));
    }
  }
  return _result;
}

std::optional<uint64_t> LoopifyOptionMaybe::safe_head(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::optional<uint64_t>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return std::make_optional<uint64_t>(a0);
  }
}

std::optional<List<uint64_t>>
LoopifyOptionMaybe::safe_tail(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::optional<List<uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return std::make_optional<List<uint64_t>>(*a1);
  }
}

List<uint64_t> LoopifyOptionMaybe::catMaybes(
    const List<std::optional<uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::optional<uint64_t>> *l;
  };

  /// _Resume_x: saves [x], resumes after recursive call with _result.
  struct _Resume_x {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_x>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified catMaybes: _Enter -> _Resume_x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::optional<uint64_t>> &l = *_f.l;
      if (std::holds_alternative<typename List<std::optional<uint64_t>>::Nil>(
              l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::optional<uint64_t>>::Cons>(l.v());
        if (a0.has_value()) {
          const uint64_t &x = *a0;
          _stack.emplace_back(_Resume_x{x});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_x>(_frame));
      _result = List<uint64_t>::cons(_f.x, std::move(_result));
    }
  }
  return _result;
}

std::optional<uint64_t>
LoopifyOptionMaybe::find_index_even_aux(const List<uint64_t> &l, uint64_t idx) {
  uint64_t _loop_idx = std::move(idx);
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
        return std::make_optional<uint64_t>(_loop_idx);
      } else {
        _loop_idx = (_loop_idx + UINT64_C(1));
        _loop_l = a1.get();
      }
    }
  }
}

std::optional<uint64_t>
LoopifyOptionMaybe::find_index_even(const List<uint64_t> &l) {
  return find_index_even_aux(l, UINT64_C(0));
}
