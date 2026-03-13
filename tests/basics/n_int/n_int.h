#ifndef INCLUDED_N_INT
#define INCLUDED_N_INT

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
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

enum class Comparison { e_EQ, e_LT, e_GT };

struct Pos {
  __attribute__((pure)) static unsigned int succ(const unsigned int x);
  __attribute__((pure)) static unsigned int pred_double(const unsigned int x);
  __attribute__((pure)) static unsigned int pred_N(const unsigned int x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      unsigned int d_a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit mask(IsNul _v) : d_v_(std::move(_v)) {}

    explicit mask(IsPos _v) : d_v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mask> IsNul_() {
        return std::shared_ptr<mask>(new mask(IsNul{}));
      }

      static std::shared_ptr<mask> IsPos_(unsigned int a0) {
        return std::shared_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::shared_ptr<mask> IsNeg_() {
        return std::shared_ptr<mask>(new mask(IsNeg{}));
      }

      static std::unique_ptr<mask> IsNul_uptr() {
        return std::unique_ptr<mask>(new mask(IsNul{}));
      }

      static std::unique_ptr<mask> IsPos_uptr(unsigned int a0) {
        return std::unique_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::unique_ptr<mask> IsNeg_uptr() {
        return std::unique_ptr<mask>(new mask(IsNeg{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  static std::shared_ptr<mask> succ_double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_pred_mask(const unsigned int x);
  static std::shared_ptr<mask> sub_mask(const unsigned int x,
                                        const unsigned int y);
  static std::shared_ptr<mask> sub_mask_carry(const unsigned int x,
                                              const unsigned int y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const unsigned int x, const unsigned int y);
  __attribute__((pure)) static Comparison compare(const unsigned int _x0,
                                                  const unsigned int _x1);
  __attribute__((pure)) static bool eqb(const unsigned int p,
                                        const unsigned int q);
};

struct Coq_Pos {
  __attribute__((pure)) static unsigned int add_carry(const unsigned int x,
                                                      const unsigned int y);
};

struct BinNat {
  __attribute__((pure)) static Comparison compare(const unsigned int n,
                                                  const unsigned int m);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  pos_div_eucl(const unsigned int a, const unsigned int b);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  div_eucl(const unsigned int a, const unsigned int b);
};

struct NIntTest {
  __attribute__((pure)) static unsigned int add_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int mul_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int sub_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int div_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static bool eqb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static bool ltb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static bool leb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static unsigned int succ_test(const unsigned int _x0);
  __attribute__((pure)) static unsigned int pred_test(const unsigned int _x0);
  __attribute__((pure)) static unsigned int double_test(const unsigned int _x0);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = (2u * (2u * 1u) + 1u);
  static inline const unsigned int big_val =
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))));
  __attribute__((pure)) static bool is_zero(const unsigned int n);
  __attribute__((pure)) static unsigned int pos_add(const unsigned int _x0,
                                                    const unsigned int _x1);
  __attribute__((pure)) static unsigned int pos_succ(const unsigned int _x0);
};

#endif // INCLUDED_N_INT
