#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Bool0 {
  struct bool0 {
  public:
    struct true0 {};
    struct false0 {};
    using variant_t = std::variant<true0, false0>;

  private:
    variant_t v_;
    explicit bool0(true0 _v) : v_(std::move(_v)) {}
    explicit bool0(false0 _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Bool0::bool0> true0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(true0{}));
      }
      static std::shared_ptr<Bool0::bool0> false0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(false0{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Comparison {
  struct cmp {
  public:
    struct CmpLt {};
    struct CmpEq {};
    struct CmpGt {};
    using variant_t = std::variant<CmpLt, CmpEq, CmpGt>;

  private:
    variant_t v_;
    explicit cmp(CmpLt _v) : v_(std::move(_v)) {}
    explicit cmp(CmpEq _v) : v_(std::move(_v)) {}
    explicit cmp(CmpGt _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<cmp> CmpLt_() {
        return std::shared_ptr<cmp>(new cmp(CmpLt{}));
      }
      static std::shared_ptr<cmp> CmpEq_() {
        return std::shared_ptr<cmp>(new cmp(CmpEq{}));
      }
      static std::shared_ptr<cmp> CmpGt_() {
        return std::shared_ptr<cmp>(new cmp(CmpGt{}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1>
  static T1 cmp_rect(const T1 f, const T1 f0, const T1 f1,
                     const std::shared_ptr<cmp> &c) {
    return std::visit(
        Overloaded{[&](const typename cmp::CmpLt _args) -> T1 { return f; },
                   [&](const typename cmp::CmpEq _args) -> T1 { return f0; },
                   [&](const typename cmp::CmpGt _args) -> T1 { return f1; }},
        c->v());
  }

  template <typename T1>
  static T1 cmp_rec(const T1 f, const T1 f0, const T1 f1,
                    const std::shared_ptr<cmp> &c) {
    return std::visit(
        Overloaded{[&](const typename cmp::CmpLt _args) -> T1 { return f; },
                   [&](const typename cmp::CmpEq _args) -> T1 { return f0; },
                   [&](const typename cmp::CmpGt _args) -> T1 { return f1; }},
        c->v());
  }

  static unsigned int cmp_to_nat(const std::shared_ptr<cmp> &c);

  static std::shared_ptr<cmp> compare_nats(const unsigned int a,
                                           const unsigned int b);

  static unsigned int max_nat(const unsigned int a, const unsigned int b);

  static unsigned int min_nat(const unsigned int a, const unsigned int b);

  static unsigned int clamp(const unsigned int val0, const unsigned int lo,
                            const unsigned int hi);

  static std::shared_ptr<cmp> flip_cmp(const std::shared_ptr<cmp> &c);

  static inline const unsigned int test_lt_nat =
      cmp_to_nat(cmp::ctor::CmpLt_());

  static inline const unsigned int test_eq_nat =
      cmp_to_nat(cmp::ctor::CmpEq_());

  static inline const unsigned int test_gt_nat =
      cmp_to_nat(cmp::ctor::CmpGt_());

  static inline const std::shared_ptr<cmp> test_compare_lt =
      compare_nats(3u, 5u);

  static inline const std::shared_ptr<cmp> test_compare_eq =
      compare_nats(5u, 5u);

  static inline const std::shared_ptr<cmp> test_compare_gt =
      compare_nats(7u, 5u);

  static inline const unsigned int test_max = max_nat(3u, 7u);

  static inline const unsigned int test_min = min_nat(3u, 7u);

  static inline const unsigned int test_clamp_lo = clamp(1u, 3u, 7u);

  static inline const unsigned int test_clamp_mid = clamp(5u, 3u, 7u);

  static inline const unsigned int test_clamp_hi = clamp(9u, 3u, 7u);

  static inline const std::shared_ptr<cmp> test_flip =
      flip_cmp(cmp::ctor::CmpLt_());
};
