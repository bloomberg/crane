#ifndef INCLUDED_SEMANTIC_FOLD
#define INCLUDED_SEMANTIC_FOLD

#include "crane_fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

/// Rewrites licensed by declared meanings (Crane Semantics): a sum over a
/// list carried forward in an accumulator, and small closed definitions
/// computed at extraction time.  Each has a counterpart that must be left as
/// written.
struct SemanticFold {
  struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      std::shared_ptr<list> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    static list nil() { return list(Nil{}); }

    static list cons(uint64_t a0, list a1) {
      return list(Cons{a0, std::make_shared<list>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 list_rect(T1 f, F1 &&f0, const list &l) {
    if (std::holds_alternative<typename list::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename F1>
  static T1 list_rec(const T1 &f, F1 &&f0, const list &l) {
    return list_rect<T1>(f, f0, l);
  }

  static list seq(uint64_t start, uint64_t len);
  /// Whitelisted: unsigned addition of a pure contribution, rewritten to a
  /// loop.  A list long enough to exhaust the stack frame by frame must sum.
  static uint64_t sum(const list &l);
  static uint64_t sum_scaled(uint64_t k, const list &l);
  /// Declined: sub is not associative.
  static uint64_t alt(const list &l);
  /// Declined: plus' is the program's own function, with no declared
  /// meaning.
  static uint64_t plus_(uint64_t x0_, uint64_t x1_);
  static uint64_t sum_(const list &l);
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(const T1 &f, const T1 &f0, const T1 &f1, Color c) {
    return color_rect<T1>(f, f0, f1, c);
  }

  static Color next(Color c);
  /// Computed at extraction time.
  static constexpr uint64_t ten_sum = UINT64_C(55);
  static constexpr uint64_t scaled = UINT64_C(22);
  static constexpr uint64_t alt_small = UINT64_C(0);
  static constexpr Color third = Color::BLUE;
  /// Too large for the evaluation budget: left as a computation.
  static inline const uint64_t big_sum =
      sum(seq(UINT64_C(0), (UINT64_C(300) * UINT64_C(100))));
};

#endif // INCLUDED_SEMANTIC_FOLD
