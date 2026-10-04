#include "loopify_conditional_recursion.h"

std::pair<uint64_t, uint64_t> LoopifyConditionalRecursion::cached_sum(
    const std::optional<uint64_t> &cache,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    std::optional<uint64_t> cache;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, cache});
  /// Loopified cached_sum: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont1{a0});
          _stack.emplace_back(
              CraneEnter{crane_raw(a1), std::optional<uint64_t>()});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
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
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    uint64_t target;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  std::pair<uint64_t, List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, target});
  /// Loopified find_or_recurse: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont1{});
          _stack.emplace_back(CraneEnter{crane_raw(a1), std::move(target)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      auto sub = std::move(_result);
      _result = std::make_pair((sub.first + UINT64_C(1)), sub.second);
    }
  }
  return _result;
}

uint64_t LoopifyConditionalRecursion::nested_cond(
    uint64_t threshold, uint64_t lo, uint64_t hi,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified nested_cond: CraneEnter -> CraneCont1.
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
              _stack.emplace_back(CraneCont1{});
              _stack.emplace_back(CraneEnter{crane_raw(a1)});
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
      auto _f = std::move(std::get<CraneCont1>(_frame));
      std::pair<uint64_t, bool> sub = std::make_pair(std::move(_result), false);
      _result =
          (sub.first + (std::move(sub).second ? UINT64_C(1) : UINT64_C(0)));
    }
  }
  return _result;
}

std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>>
LoopifyConditionalRecursion::multi_return(
    const std::optional<std::pair<uint64_t, uint64_t>> &memo,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    std::optional<std::pair<uint64_t, uint64_t>> memo;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  std::pair<uint64_t, std::optional<std::pair<uint64_t, uint64_t>>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, memo});
  /// Loopified multi_return: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      const std::optional<std::pair<uint64_t, uint64_t>> memo = _f.memo;
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
              const auto &[a, b] = p;
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
          _stack.emplace_back(CraneCont1{a0});
          _stack.emplace_back(CraneEnter{
              crane_raw(a1), std::optional<std::pair<uint64_t, uint64_t>>()});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      uint64_t count = sub.first;
      std::optional<std::pair<uint64_t, uint64_t>> payload =
          std::move(sub).second;
      if (payload.has_value()) {
        const std::pair<uint64_t, uint64_t> &p = *payload;
        const auto &[a, b] = p;
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
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
    uint64_t key;
  };

  /// CraneCont1: saves [a0], resumes after recursive call, then processes rest.
  struct CraneCont1 {
    uint64_t a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l, key});
  /// Loopified accum_with_cache: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
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
          _stack.emplace_back(CraneCont1{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1), std::move(key)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      uint64_t a0 = _f.a0;
      auto sub = std::move(_result);
      _result = std::make_pair((sub.first + a0), (sub.second + UINT64_C(1)));
    }
  }
  return _result;
}
