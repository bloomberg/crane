#include "loopify_conditional_recursion.h"

std::pair<uint64_t, uint64_t>
LoopifyConditionalRecursion::cached_sum(const std::optional<uint64_t> &cache,
                                        const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of cached_sum: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    std::optional<uint64_t> cache;
  };

  struct _after_cached_sum_in_None {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_cached_sum_in_None>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, cache});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      const std::optional<uint64_t> cache = _f.cache;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        std::pair<uint64_t, uint64_t> sub;
        if (cache.has_value()) {
          const uint64_t &v = *cache;
          sub = std::make_pair(v, UINT64_C(0));
          {
            _result =
                std::make_pair((a0 + sub.first), (sub.second + UINT64_C(1)));
          }
        } else {
          _stack.emplace_back(_after_cached_sum_in_None{a0});
          _stack.emplace_back(_call{crane_raw(a1), std::optional<uint64_t>()});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_cached_sum_in_None>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      _result = std::make_pair((a0 + sub.first), (sub.second + UINT64_C(1)));
    }
  }
  return _result;
}

std::pair<uint64_t, List<uint64_t>>
LoopifyConditionalRecursion::find_or_recurse(uint64_t target,
                                             const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of find_or_recurse: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_find_or_recurse_in_false {};

  using _frame = std::variant<_call, _after_find_or_recurse_in_false>;
  std::pair<uint64_t, List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        std::pair<uint64_t, List<uint64_t>> sub;
        if (a0 == target) {
          sub = std::make_pair(a0, *a1);
          {
            _result = std::make_pair((std::move(sub).first + UINT64_C(1)),
                                     std::move(sub).second);
          }
        } else {
          _stack.emplace_back(_after_find_or_recurse_in_false{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_find_or_recurse_in_false>(_popped));
      _stack.pop_back();
      auto sub = std::move(_result);
      _result = std::make_pair((std::move(sub).first + UINT64_C(1)),
                               std::move(sub).second);
    }
  }
  return _result;
}

uint64_t
LoopifyConditionalRecursion::nested_cond(uint64_t threshold, uint64_t lo,
                                         uint64_t hi, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of nested_cond: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_nested_cond_in_true {};

  using _frame = std::variant<_call, _after_nested_cond_in_true>;
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
        std::pair<uint64_t, bool> sub;
        if (lo <= a0) {
          if (a0 <= hi) {
            sub = std::make_pair(a0, true);
            {
              _result = (sub.first + (sub.second ? UINT64_C(1) : UINT64_C(0)));
            }
          } else {
            if (a0 <= threshold) {
              _stack.emplace_back(_after_nested_cond_in_true{});
              _stack.emplace_back(_call{crane_raw(a1)});
            } else {
              sub = std::make_pair(UINT64_C(0), true);
              {
                _result =
                    (sub.first + (sub.second ? UINT64_C(1) : UINT64_C(0)));
              }
            }
          }
        } else {
          sub = std::make_pair(UINT64_C(0), true);
          {
            _result = (sub.first + (sub.second ? UINT64_C(1) : UINT64_C(0)));
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_after_nested_cond_in_true>(_popped));
      _stack.pop_back();
      std::pair<uint64_t, bool> sub = std::make_pair(std::move(_result), false);
      _result = (sub.first + (sub.second ? UINT64_C(1) : UINT64_C(0)));
    }
  }
  return _result;
}

std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>>
LoopifyConditionalRecursion::multi_return(
    const std::optional<std::pair<uint64_t, uint64_t>> &memo,
    const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of multi_return: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
    std::optional<std::pair<uint64_t, uint64_t>> memo;
  };

  struct _after_multi_return_in_None {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_multi_return_in_None>;
  std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l, memo});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      const std::optional<std::pair<uint64_t, uint64_t>> memo = _f.memo;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result =
            std::make_pair(UINT64_C(0),
                           std::optional<std::pair<uint64_t, uint64_t>>());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>> sub;
        if (memo.has_value()) {
          const std::pair<uint64_t, uint64_t> &p = *memo;
          sub = std::make_pair(
              UINT64_C(0),
              std::make_optional<std::pair<uint64_t, uint64_t>>(p));
          {
            uint64_t count = sub.first;
            std::optional<std::pair<uint64_t, uint64_t>> payload = sub.second;
            if (payload.has_value()) {
              const std::pair<uint64_t, uint64_t> &p = *payload;
              const auto &[a, b] = p;
              _result =
                  std::make_pair(
                      (count + UINT64_C(1)),
                      std::make_optional<std::pair<uint64_t, uint64_t>>(
                          std::make_pair((a + a0), b)));
            } else {
              _result = std::make_pair(
                  (count + UINT64_C(1)),
                  std::optional<std::pair<uint64_t, uint64_t>>());
            }
          }
        } else {
          _stack.emplace_back(_after_multi_return_in_None{a0});
          _stack.emplace_back(_call{
              crane_raw(a1), std::optional<std::pair<uint64_t, uint64_t>>()});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_multi_return_in_None>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      uint64_t count = sub.first;
      std::optional<std::pair<uint64_t, uint64_t>> payload = sub.second;
      if (payload.has_value()) {
        const std::pair<uint64_t, uint64_t> &p = *payload;
        const auto &[a, b] = p;
        _result = std::make_pair(
            (count + UINT64_C(1)),
            std::make_optional<std::pair<uint64_t, uint64_t>>(
                std::make_pair((a + a0), b)));
      } else {
        _result =
            std::make_pair((count + UINT64_C(1)),
                           std::optional<std::pair<uint64_t, uint64_t>>());
      }
    }
  }
  return _result;
}

std::pair<uint64_t, uint64_t>
LoopifyConditionalRecursion::accum_with_cache(uint64_t key,
                                              const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of accum_with_cache: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_accum_with_cache_in_None {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_accum_with_cache_in_None>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        std::optional<uint64_t> cached;
        if (a0 == key) {
          cached = std::make_optional<uint64_t>((a0 * UINT64_C(2)));
        } else {
          cached = std::optional<uint64_t>();
        }
        std::pair<uint64_t, uint64_t> sub;
        if (cached.has_value()) {
          const uint64_t &v = *cached;
          sub = std::make_pair(v, UINT64_C(0));
          {
            _result =
                std::make_pair((sub.first + a0), (sub.second + UINT64_C(1)));
          }
        } else {
          _stack.emplace_back(_after_accum_with_cache_in_None{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_accum_with_cache_in_None>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      _result = std::make_pair((sub.first + a0), (sub.second + UINT64_C(1)));
    }
  }
  return _result;
}
