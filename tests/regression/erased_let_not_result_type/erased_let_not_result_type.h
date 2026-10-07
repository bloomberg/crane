#ifndef INCLUDED_ERASED_LET_NOT_RESULT_TYPE
#define INCLUDED_ERASED_LET_NOT_RESULT_TYPE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

template <typename M>
concept SYMS = requires {
  typename M::semty;
  {
    M::cast(std::declval<uint64_t>(), std::declval<uint64_t>(),
            std::declval<crane::obj>())
  } -> std::same_as<crane::obj>;
  { M::default_(std::declval<uint64_t>()) } -> std::same_as<crane::obj>;
  {
    M::size(std::declval<uint64_t>(), std::declval<crane::obj>())
  } -> std::same_as<uint64_t>;
};

struct ErasedLetNotResultType {
  template <SYMS S> struct Parser {
    struct result {
      // TYPES
      struct Unique {
        crane::obj a0;
      };

      struct Ambig {
        crane::obj a0;
      };

      struct Reject {
        uint64_t a0;
      };

      using variant_t = std::variant<Unique, Ambig, Reject>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      result() {}

      explicit result(Unique _v) : v_(std::move(_v)) {}

      explicit result(Ambig _v) : v_(std::move(_v)) {}

      explicit result(Reject _v) : v_(std::move(_v)) {}

      static result unique(crane::obj a0) {
        return result(Unique{std::move(a0)});
      }

      static result ambig(crane::obj a0) {
        return result(Ambig{std::move(a0)});
      }

      static result reject(uint64_t a0) { return result(Reject{a0}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }
    };

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F3 &, const uint64_t &>
    static T1 result_rect(uint64_t, F1 &&f, F2 &&f0, F3 &&f1, const result &r) {
      if (std::holds_alternative<typename result::Unique>(r.v())) {
        const auto &[a0] = std::get<typename result::Unique>(r.v());
        return crane_call_erased(f, a0);
      } else if (std::holds_alternative<typename result::Ambig>(r.v())) {
        const auto &[a0] = std::get<typename result::Ambig>(r.v());
        return crane_call_erased(f0, a0);
      } else {
        const auto &[a0] = std::get<typename result::Reject>(r.v());
        return f1(a0);
      }
    }

    template <typename T1, typename F1, typename F2, typename F3>
    static T1 result_rec(uint64_t _x, F1 &&f, F2 &&f0, F3 &&f1,
                         const result &r) {
      return result_rect<T1>(_x, crane_erase_fn<T1>(f), crane_erase_fn<T1>(f0),
                             f1, r);
    }

    static result finish(uint64_t x, uint64_t x_, bool un, crane::obj v_) {
      if (Nat::eq_dec(x_, x)) {
        auto v = S::cast(x_, x, v_);
        if (un) {
          return result::unique(std::move(v));
        } else {
          return result::ambig(std::move(v));
        }
      } else {
        return result::reject(UINT64_C(1));
      }
    }

    static uint64_t measure(uint64_t x, const result &r) {
      if (std::holds_alternative<typename result::Unique>(r.v())) {
        const auto &[a0] = std::get<typename result::Unique>(r.v());
        return S::size(x, a0);
      } else if (std::holds_alternative<typename result::Ambig>(r.v())) {
        const auto &[a0] = std::get<typename result::Ambig>(r.v());
        return (UINT64_C(100) + S::size(x, a0));
      } else {
        const auto &[a0] = std::get<typename result::Reject>(r.v());
        return (UINT64_C(1000) + a0);
      }
    }
  };

  struct Syms {
    using semty = crane::obj;
    static semty cast(uint64_t _x, uint64_t _x0, semty v);
    static semty default_(uint64_t n);
    static uint64_t size(uint64_t n, semty b);
  };

  using P = Parser<Syms>;
  static inline const uint64_t run =
      ((P::measure(UINT64_C(3),
                   P::finish(UINT64_C(3), UINT64_C(3), true, UINT64_C(7))) +
        P::measure(UINT64_C(3),
                   P::finish(UINT64_C(3), UINT64_C(3), false, UINT64_C(7)))) +
       P::measure(UINT64_C(3),
                  P::finish(UINT64_C(3), UINT64_C(4), true, UINT64_C(7))));
};

#endif // INCLUDED_ERASED_LET_NOT_RESULT_TYPE
