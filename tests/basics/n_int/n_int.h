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

enum class comparison { Eq, Lt, Gt };

struct Pos {
  static unsigned int succ(const unsigned int x);
  static unsigned int pred_double(const unsigned int x);
  static unsigned int pred_N(const unsigned int x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      unsigned int _a0;
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
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static std::shared_ptr<mask> succ_double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_pred_mask(const unsigned int x);
  static std::shared_ptr<mask> sub_mask(const unsigned int x,
                                        const unsigned int y);
  static std::shared_ptr<mask> sub_mask_carry(const unsigned int x,
                                              const unsigned int y);
  static comparison compare_cont(const comparison r, const unsigned int x,
                                 const unsigned int y);
  static comparison compare(const unsigned int _x0, const unsigned int _x1);
  static bool eqb(const unsigned int p, const unsigned int q);
};

struct Coq_Pos {
  static unsigned int add_carry(const unsigned int x, const unsigned int y);
};

struct BinNat {
  static comparison compare(const unsigned int n, const unsigned int m);
  static std::pair<unsigned int, unsigned int>
  pos_div_eucl(const unsigned int a, const unsigned int b);
  static std::pair<unsigned int, unsigned int> div_eucl(const unsigned int a,
                                                        const unsigned int b);
};

struct NIntTest {
  static unsigned int add_test(const unsigned int _x0, const unsigned int _x1);
  static unsigned int mul_test(const unsigned int _x0, const unsigned int _x1);
  static unsigned int sub_test(const unsigned int _x0, const unsigned int _x1);
  static unsigned int div_test(const unsigned int _x0, const unsigned int _x1);
  static bool eqb_test(const unsigned int _x0, const unsigned int _x1);
  static bool ltb_test(const unsigned int _x0, const unsigned int _x1);
  static bool leb_test(const unsigned int _x0, const unsigned int _x1);
  static unsigned int succ_test(const unsigned int _x0);
  static unsigned int pred_test(const unsigned int _x0);
  static unsigned int double_test(const unsigned int _x0);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = (2u * (2u * 1u) + 1u);
  static inline const unsigned int big_val =
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))));
  static bool is_zero(const unsigned int n);
  static unsigned int pos_add(const unsigned int _x0, const unsigned int _x1);
  static unsigned int pos_succ(const unsigned int _x0);
};
