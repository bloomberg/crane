#include <loopify_option_maybe.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_even(const std::shared_ptr<List<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_optional<unsigned int>(d_a0);
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_greater(const unsigned int threshold,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (threshold < d_a0) {
        _result = std::make_optional<unsigned int>(d_a0);
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int> LoopifyOptionMaybe::lookup(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (key == k) {
        _result = std::make_optional<unsigned int>(v);
        _continue = false;
      } else {
        _loop_l = d_a1;
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyOptionMaybe::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (key == k) {
        auto _cell = List<unsigned int>::cons(v, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = d_a1;
        continue;
      } else {
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::safe_head(const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    return std::make_optional<unsigned int>(d_a0);
  }
}

__attribute__((pure)) std::optional<std::shared_ptr<List<unsigned int>>>
LoopifyOptionMaybe::safe_tail(const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return std::optional<std::shared_ptr<List<unsigned int>>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    return std::make_optional<std::shared_ptr<List<unsigned int>>>(d_a1);
  }
}

std::shared_ptr<List<unsigned int>> LoopifyOptionMaybe::catMaybes(
    const std::shared_ptr<List<std::optional<unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::optional<unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<std::optional<unsigned int>>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::optional<unsigned int>>::Cons>(
              _loop_l->v());
      if (d_a0.has_value()) {
        const unsigned int &x = *d_a0;
        auto _cell = List<unsigned int>::cons(x, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = d_a1;
        continue;
      } else {
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even_aux(
    const std::shared_ptr<List<unsigned int>> &l, const unsigned int idx) {
  std::optional<unsigned int> _result;
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = std::optional<unsigned int>();
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if ((2u ? d_a0 % 2u : d_a0) == 0u) {
        _result = std::make_optional<unsigned int>(_loop_idx);
        _continue = false;
      } else {
        unsigned int _next_idx = (_loop_idx + 1u);
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        _loop_idx = std::move(_next_idx);
        _loop_l = std::move(_next_l);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::optional<unsigned int>
LoopifyOptionMaybe::find_index_even(
    const std::shared_ptr<List<unsigned int>> &l) {
  return find_index_even_aux(l, 0u);
}
