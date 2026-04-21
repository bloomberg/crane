#ifndef INCLUDED_ROCQ_BUG_4720
#define INCLUDED_ROCQ_BUG_4720

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename M>
concept A = requires { typename M::t; };
template <typename M>
concept B = true;
template <typename M>
concept C = requires { requires A<typename M::a>; };

struct RocqBug4720 {
  struct A_instance {
    using t = std::shared_ptr<Nat>;
  };

  struct A_private {
    using t = std::shared_ptr<Nat>;
  };

  static_assert(A<A_private>);

  template <A a_, B b_, typename c_> struct WithMod {};

  template <A a_, B b_, typename c_> struct WithDef {};

  template <A a_, B b_, typename c_> struct WithModPriv {};
};

#endif // INCLUDED_ROCQ_BUG_4720
