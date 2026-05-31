#include "loopify_conditional_recursion.h"

std::pair<uint64_t, uint64_t> LoopifyConditionalRecursion::cached_sum(
    const std::optional<uint64_t> &cache,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    std::optional<uint64_t> cache;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, cache});
  /// Loopified cached_sum: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      const std::optional<uint64_t> &cache = _f.cache;
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
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(_Enter{a1.get(), std::optional<uint64_t>()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      _result = std::make_pair((a0 + sub.first), (sub.second + UINT64_C(1)));
    }
  }
  return _result;
}

std::pair<uint64_t, List<uint64_t>>
LoopifyConditionalRecursion::find_or_recurse(
    uint64_t target,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t target;
  };

  /// _Cont1: resumes after recursive call, then processes rest.
  struct _Cont1 {};

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<uint64_t, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, target});
  /// Loopified find_or_recurse: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t target = _f.target;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(UINT64_C(0), List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        std::pair<uint64_t, List<uint64_t>> sub;
        if (a0 == target) {
          sub = std::make_pair(a0, *a1);
          {
            _result = std::make_pair((sub.first + UINT64_C(1)), sub.second);
          }
        } else {
          _stack.emplace_back(_Cont1{});
          _stack.emplace_back(_Enter{a1.get(), std::move(target)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      auto sub = std::move(_result);
      _result = std::make_pair((sub.first + UINT64_C(1)), sub.second);
    }
  }
  return _result;
}

uint64_t LoopifyConditionalRecursion::nested_cond(
    uint64_t threshold, uint64_t lo, uint64_t hi,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont1: saves [_s0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    std::decay_t<decltype(false)> _s0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified nested_cond: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
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
              _result = (sub.first +
                         (std::move(sub).second ? UINT64_C(1) : UINT64_C(0)));
            }
          } else {
            if (a0 <= threshold) {
              _stack.emplace_back(_Cont1{false});
              _stack.emplace_back(_Enter{a1.get()});
            } else {
              sub = std::make_pair(UINT64_C(0), true);
              {
                _result = (sub.first +
                           (std::move(sub).second ? UINT64_C(1) : UINT64_C(0)));
              }
            }
          }
        } else {
          sub = std::make_pair(UINT64_C(0), true);
          {
            _result = (sub.first +
                       (std::move(sub).second ? UINT64_C(1) : UINT64_C(0)));
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      auto sub = std::make_pair(std::move(_result), _f._s0);
      _result =
          (sub.first + (std::move(sub).second ? UINT64_C(1) : UINT64_C(0)));
    }
  }
  return _result;
}

std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>>
LoopifyConditionalRecursion::multi_return(
    const std::optional<std::pair<uint64_t, uint64_t>> &memo,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    std::optional<std::pair<uint64_t, uint64_t>> memo;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, memo});
  /// Loopified multi_return: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      const std::optional<std::pair<uint64_t, uint64_t>> &memo = _f.memo;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = std::make_pair(
            UINT64_C(0), std::optional<std::pair<uint64_t, uint64_t>>());
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
            std::optional<std::pair<uint64_t, uint64_t>> payload =
                std::move(sub).second;
            if (payload.has_value()) {
              const std::pair<uint64_t, uint64_t> &p = *payload;
              const uint64_t &a = p.first;
              const uint64_t &b = p.second;
              _result = std::make_pair(
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
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(
              _Enter{a1.get(), std::optional<std::pair<uint64_t, uint64_t>>()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      uint64_t count = sub.first;
      std::optional<std::pair<uint64_t, uint64_t>> payload =
          std::move(sub).second;
      if (payload.has_value()) {
        const std::pair<uint64_t, uint64_t> &p = *payload;
        const uint64_t &a = p.first;
        const uint64_t &b = p.second;
        _result =
            std::make_pair((count + UINT64_C(1)),
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

std::pair<uint64_t, uint64_t> LoopifyConditionalRecursion::accum_with_cache(
    uint64_t key,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t key;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, key});
  /// Loopified accum_with_cache: _Enter -> _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t key = _f.key;
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
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(_Enter{a1.get(), std::move(key)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      _result = std::make_pair((sub.first + a0), (sub.second + UINT64_C(1)));
    }
  }
  return _result;
}
