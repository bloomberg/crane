#ifndef INCLUDED_ROCQ_BUG_4844
#define INCLUDED_ROCQ_BUG_4844

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A, typename t_B> struct Sum {
  // TYPES
  struct Inl {
    t_A d_a0;
  };

  struct Inr {
    t_B d_a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sum(Inl _v) : d_v_(std::move(_v)) {}

  explicit Sum(Inr _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sum<t_A, t_B>> inl(t_A a0) {
    return std::make_shared<Sum<t_A, t_B>>(Inl{std::move(a0)});
  }

  static std::shared_ptr<Sum<t_A, t_B>> inr(t_B a0) {
    return std::make_shared<Sum<t_A, t_B>>(Inr{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RocqBug4844 {
  static inline const std::shared_ptr<Sum<std::any, std::any>> semilogic =
      Sum<std::any, std::any>::inl(std::any{});
  enum class SomeType { e_BUILD_SOMETYPE };
  using ST = std::any;
  static inline const SomeType SomeTrue = SomeType::e_BUILD_SOMETYPE;
  using abstrSum = std::shared_ptr<Sum<ST, ST>>;
  static inline const abstrSum semilogic_ = std::any_cast<abstrSum>(semilogic);

  struct box {
    // TYPES
    struct Box0 {
      std::shared_ptr<Sum<ST, ST>> d_a0;
    };

    using variant_t = std::variant<Box0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<box> box0(const std::shared_ptr<Sum<ST, ST>> &a0) {
      return std::make_shared<box>(Box0{a0});
    }

    static std::shared_ptr<box> box0(std::shared_ptr<Sum<ST, ST>> &&a0) {
      return std::make_shared<box>(Box0{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<Sum<ST, ST>>> F1>
  static T1 box_rect(const SomeType, F1 &&f, const std::shared_ptr<box> &b) {
    const auto &[d_a0] = std::get<typename box::Box0>(b->v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Sum<ST, ST>>> F1>
  static T1 box_rec(const SomeType, F1 &&f, const std::shared_ptr<box> &b) {
    const auto &[d_a0] = std::get<typename box::Box0>(b->v());
    return f(d_a0);
  }

  static inline const std::shared_ptr<box> boxed_semilogic =
      box::box0(semilogic);
};

#endif // INCLUDED_ROCQ_BUG_4844
