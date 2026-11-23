#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <deque>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

#include "crane_bake.h"
extern const crane::bake::image crane_baked_labelled_ebb90243a587;
extern const crane::bake::image crane_baked_digits_c080c1cf345d;
extern const crane::bake::image crane_baked_word_81b07524450d;
extern const crane::bake::image crane_baked_half_1b93d6b8118f;
extern const crane::bake::image crane_baked_deep_a469784f0b1a;
extern const crane::bake::image crane_baked_arr_c0b98965956e;

struct BakeMappedValues {
  static inline const persistent_array<uint64_t> arr =
      crane::bake::read<persistent_array<uint64_t>>(
          crane_baked_arr_c0b98965956e);
  static inline const std::optional<std::pair<std::string, uint64_t>> labelled =
      crane::bake::read<std::optional<std::pair<std::string, uint64_t>>>(
          crane_baked_labelled_ebb90243a587);
  static inline const std::deque<uint64_t> digits =
      crane::bake::read<std::deque<uint64_t>>(crane_baked_digits_c080c1cf345d);
  static inline const int64_t word =
      crane::bake::read<int64_t>(crane_baked_word_81b07524450d);
  static inline const double half =
      crane::bake::read<double>(crane_baked_half_1b93d6b8118f);

  struct spine {
    // TYPES
    struct Root {};

    struct Grow {
      std::shared_ptr<spine> rest;
      uint64_t x;
    };

    using variant_t = std::variant<Root, Grow>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    spine() {}

    explicit spine(Root _v) : v_(_v) {}

    explicit spine(Grow _v) : v_(std::move(_v)) {}

    static spine root() { return spine(Root{}); }

    static spine grow(crane::shared_child_slot<spine> rest, uint64_t x) {
      return spine(Grow{rest.take(), x});
    }

    // MANIPULATORS
    ~spine() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<spine> {
        if (auto *_alt = std::get_if<Grow>(&_v)) {
          if (_alt->rest && _alt->rest.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->rest);
          }
        }
        return nullptr;
      };
      std::shared_ptr<spine> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    spine(const spine &) = default;
    spine &operator=(const spine &) = default;
    spine(spine &&) = default;
    spine &operator=(spine &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 spine_rect(T1 f, F1 &&f0, const spine &s) {
    // Explicit stack replaces the non-tail recursion of spine_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const spine *s;
    };

    struct _after_spine_rect_in_Grow {
      std::shared_ptr<spine> rest0;
      uint64_t x0;
    };

    using _frame = std::variant<_call, _after_spine_rect_in_Grow>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&s});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const spine &s = *_f.s;
        if (std::holds_alternative<typename spine::Root>(s.v())) {
          _result = f;
        } else {
          const auto &[rest0, x0] = std::get<typename spine::Grow>(s.v());
          _stack.emplace_back(_after_spine_rect_in_Grow{rest0, x0});
          _stack.emplace_back(_call{crane_raw(rest0)});
        }
      } else {
        auto _f = std::move(std::get<_after_spine_rect_in_Grow>(_popped));
        _stack.pop_back();
        std::shared_ptr<spine> rest0 = std::move(_f.rest0);
        uint64_t x0 = _f.x0;
        _result = f0(*rest0, std::move(_result), x0);
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 spine_rec(T1 f, F1 &&f0, const spine &s) {
    return spine_rect<T1>(std::move(f), f0, s);
  }

  static inline const spine deep =
      crane::bake::read<spine>(crane_baked_deep_a469784f0b1a);
  static uint64_t weight(const spine &s);
  static inline const uint64_t arr_sum =
      ((arr.get(INT64_C(0)) + arr.get(INT64_C(1))) + arr.get(INT64_C(9)));
  static inline const uint64_t label_length = []() -> uint64_t {
    if (labelled.has_value()) {
      const std::pair<std::string, uint64_t> &p = *labelled;
      const auto &[s, n] = p;
      if (static_cast<int64_t>(s.size()) == INT64_C(5)) {
        return (n + UINT64_C(5));
      } else {
        return n;
      }
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const uint64_t digits_sum =
      [](auto _f, const auto &_l, auto _a) {
        for (const auto &_x : _l) _a = _f(_a, _x);
        return _a;
      }([](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
        digits, UINT64_C(0));
  static inline const uint64_t deep_weight = weight(deep);
};
