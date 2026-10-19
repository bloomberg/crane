#ifndef INCLUDED_REUSE_ARM_FIELD_USED_TWICE
#define INCLUDED_REUSE_ARM_FIELD_USED_TWICE

#include <cstdint>
#include <memory>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "rc.h"

struct ReuseArmFieldUsedTwice {
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      crane::rc<lst> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

    static lst cons(uint64_t a0, crane::child_slot<lst> a1) {
      return lst(Cons{a0, a1.take()});
    }

    static lst cons_crane_reuse(crane::rc<lst> _tok, uint64_t a0, lst a1) {
      return lst(Cons{
          a0, crane::make_rc_reusing<lst>(std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> crane::rc<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      crane::rc<lst> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 lst_rect(T1 f, F1 &&f0, const lst &l) {
    if (std::holds_alternative<typename lst::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
      return f0(a0, *a1, lst_rect<T1>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename F1>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    return lst_rect<T1>(std::move(f), f0, l);
  }

  static uint64_t len(const lst &l);
  static lst app2(lst a, lst b);
  static lst dbl(lst l);
  static lst pairs(lst l);
  static uint64_t sum(const lst &l);
  static inline const lst l3 = lst::cons(
      UINT64_C(1), lst::cons(UINT64_C(2), lst::cons(UINT64_C(3), lst::nil())));
  static inline const uint64_t dbl_len = len(dbl(l3));
  static inline const uint64_t pairs_sum = sum(pairs(l3));
};

#endif // INCLUDED_REUSE_ARM_FIELD_USED_TWICE
