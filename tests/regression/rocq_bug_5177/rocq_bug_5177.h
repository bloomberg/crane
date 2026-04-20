#ifndef INCLUDED_ROCQ_BUG_5177
#define INCLUDED_ROCQ_BUG_5177

#include <concepts>
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
concept T = requires { typename M::t; };
template <typename M>
concept A = requires {
  typename M::t1;
  typename M::t2;
  {
    M::bar(std::declval<typename M::MT::t>(), std::declval<typename M::t1>())
  } -> std::same_as<typename M::t2>;
};

struct RocqBug5177 {
  template <T MT> struct MakeA {
    using t1 = std::shared_ptr<Nat>;
    using t2 = std::shared_ptr<Nat>;

    __attribute__((pure)) static t1 bar(const typename MT::t,
                                        std::shared_ptr<Nat> x) {
      return x;
    }
  };
};

#endif // INCLUDED_ROCQ_BUG_5177
