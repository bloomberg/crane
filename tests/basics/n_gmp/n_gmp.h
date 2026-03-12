#ifndef INCLUDED_N_GMP
#define INCLUDED_N_GMP

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <gmpxx.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class comparison { Eq, Lt, Gt };

struct Pos {
  static mpz_class succ(const mpz_class x);
  static mpz_class pred_double(const mpz_class x);
  static mpz_class pred_N(const mpz_class x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      mpz_class _a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit mask(IsNul _v) : v_(std::move(_v)) {}

    explicit mask(IsPos _v) : v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mask> IsNul_() {
        return std::shared_ptr<mask>(new mask(IsNul{}));
      }

      static std::shared_ptr<mask> IsPos_(mpz_class a0) {
        return std::shared_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::shared_ptr<mask> IsNeg_() {
        return std::shared_ptr<mask>(new mask(IsNeg{}));
      }

      static std::unique_ptr<mask> IsNul_uptr() {
        return std::unique_ptr<mask>(new mask(IsNul{}));
      }

      static std::unique_ptr<mask> IsPos_uptr(mpz_class a0) {
        return std::unique_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::unique_ptr<mask> IsNeg_uptr() {
        return std::unique_ptr<mask>(new mask(IsNeg{}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static std::shared_ptr<mask> succ_double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_pred_mask(const mpz_class x);
  static std::shared_ptr<mask> sub_mask(const mpz_class x, const mpz_class y);
  static std::shared_ptr<mask> sub_mask_carry(const mpz_class x,
                                              const mpz_class y);
  static comparison compare_cont(const comparison r, const mpz_class x,
                                 const mpz_class y);
  static comparison compare(const mpz_class _x0, const mpz_class _x1);
  static bool eqb(const mpz_class p, const mpz_class q);
};

struct Coq_Pos {
  static mpz_class add_carry(const mpz_class x, const mpz_class y);
};

struct BinNat {
  static comparison compare(const mpz_class n, const mpz_class m);
  static std::pair<mpz_class, mpz_class> pos_div_eucl(const mpz_class a,
                                                      const mpz_class b);
  static std::pair<mpz_class, mpz_class> div_eucl(const mpz_class a,
                                                  const mpz_class b);
};

struct NGMPTest {
  static mpz_class add_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class mul_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class sub_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class div_test(const mpz_class _x0, const mpz_class _x1);
  static bool eqb_test(const mpz_class _x0, const mpz_class _x1);
  static bool ltb_test(const mpz_class _x0, const mpz_class _x1);
  static bool leb_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class succ_test(const mpz_class _x0);
  static mpz_class pred_test(const mpz_class _x0);
  static mpz_class double_test(const mpz_class _x0);
  static inline const mpz_class zero_val = mpz_class(0);
  static inline const mpz_class five_val = (2 * (2 * mpz_class(1)) + 1);
  static inline const mpz_class big_val =
      (2 *
       (2 *
        (2 * (2 * (2 * (2 * (2 * (2 * (2 * mpz_class(1) + 1) + 1) + 1) + 1)) +
              1))));
  static bool is_zero(const mpz_class n);
  static mpz_class pos_add(const mpz_class _x0, const mpz_class _x1);
  static mpz_class pos_succ(const mpz_class _x0);
};

#endif // INCLUDED_N_GMP
