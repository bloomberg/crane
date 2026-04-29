#include <loopify_option_maybe.h>

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_even(const List<unsigned int> &l) {
  std::optional<unsigned int> _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_optional<unsigned int>(d_a0);
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_greater(const unsigned int &threshold,
                                 const List<unsigned int> &l) {
  std::optional<unsigned int> _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (threshold < d_a0) {
        _result = std::make_optional<unsigned int>(d_a0);
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int> LoopifyOptionMaybe::lookup(
    const unsigned int &key,
    const List<std::pair<unsigned int, unsigned int>> &l) {
  std::optional<unsigned int> _result;
  const List<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (key == k) {
        _result = std::make_optional<unsigned int>(v);
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int> LoopifyOptionMaybe::lookup_all(
    const unsigned int &key,
    const List<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<std::pair<unsigned int, unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l.v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (key == k) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(v, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      } else {
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::safe_head(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return std::make_optional<unsigned int>(d_a0);
  }
}

__attribute__((pure)) std::optional<List<unsigned int>>
LoopifyOptionMaybe::safe_tail(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::optional<List<unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return std::make_optional<List<unsigned int>>(*(d_a1));
  }
}

__attribute__((pure)) List<unsigned int>
LoopifyOptionMaybe::catMaybes(const List<std::optional<unsigned int>> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<std::optional<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<unsigned int>>::Nil>(
            _loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::optional<unsigned int>>::Cons>(
              _loop_l.v());
      if (d_a0.has_value()) {
        const unsigned int &x = *d_a0;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(x, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      } else {
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even_aux(const List<unsigned int> &l,
                                        unsigned int idx) {
  std::optional<unsigned int> _result;
  unsigned int _loop_idx = std::move(idx);
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_optional<unsigned int>(_loop_idx);
        break;
      } else {
        unsigned int _next_idx = (_loop_idx + 1u);
        const List<unsigned int> *_next_l = d_a1.get();
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even(const List<unsigned int> &l) {
  return find_index_even_aux(l, 0u);
}
