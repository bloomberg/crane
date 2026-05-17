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

List<uint64_t>
LoopifyOptionMaybe::lookup_all(uint64_t key,
                               const List<std::pair<uint64_t, uint64_t>> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
              _loop_l->v());
      const uint64_t &k = a0.first;
      const uint64_t &v = a0.second;
      if (key == k) {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(v, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
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

List<uint64_t>
LoopifyOptionMaybe::catMaybes(const List<std::optional<uint64_t>> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<std::optional<uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<std::optional<uint64_t>>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::optional<uint64_t>>::Cons>(_loop_l->v());
      if (a0.has_value()) {
        const uint64_t &x = *a0;
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
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
