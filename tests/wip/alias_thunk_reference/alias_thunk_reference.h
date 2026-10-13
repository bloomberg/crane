#ifndef INCLUDED_ALIAS_THUNK_REFERENCE
#define INCLUDED_ALIAS_THUNK_REFERENCE

#include "fn.h"
#include "lazy.h"
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

struct AliasThunkReference {
  struct A {
    struct stream {
      // TYPES
      template <typename CraneS0 = stream> struct Cons_ {
        uint64_t a0;
        CraneS0 a1;
      };

      using Cons = Cons_<>;
      using variant_t = std::variant<Cons>;

    private:
      // DATA
      crane::lazy<variant_t> lazy_v_;

    public:
      // CREATORS
      stream() {}

      explicit stream(Cons _v)
          : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

      explicit stream(crane::fn<variant_t()> _thunk)
          : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

      static stream cons(uint64_t a0, stream a1) {
        return stream(crane::lazy<variant_t>(
            std::in_place, std::in_place_index<0>, a0, std::move(a1)));
      }

      explicit stream(crane::lazy<variant_t> _cell)
          : lazy_v_(std::move(_cell)) {}

      template <typename F> static stream lazy_(F &&thunk) {
        return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
      }

      // ACCESSORS
      const variant_t &v() const { return lazy_v_.force(); }

      const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
    };

    static stream ones();
    static uint64_t hd(const stream &s);
    static uint64_t absurd_nat();
  };

  using B = A;
  static inline const uint64_t from_cofix = B::hd(B::ones);
  static inline const uint64_t from_throwing =
      (Nat::eq_dec(UINT64_C(0), UINT64_C(1)) ? B::absurd_nat : UINT64_C(9));
};

#endif // INCLUDED_ALIAS_THUNK_REFERENCE
