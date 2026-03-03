#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct Sig {
public:
  struct exist {
    A _a0;
  };
  using variant_t = std::variant<exist>;

private:
  variant_t v_;
  explicit Sig(exist _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<Sig<A>> exist_(A a0) {
      return std::shared_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
    static std::unique_ptr<Sig<A>> exist_uptr(A a0) {
      return std::unique_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct Opaque {
  static unsigned int safe_pred(const unsigned int n);

  static unsigned int pred_of_succ(const unsigned int n);

  static bool nat_eq_dec(const unsigned int n, const unsigned int x);

  static bool are_equal(const unsigned int n, const unsigned int m);

  static std::shared_ptr<Sig<unsigned int>>
  bounded_add(const unsigned int, const unsigned int, const unsigned int);

  static inline const unsigned int test_safe_pred =
      safe_pred((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_pred_succ =
      pred_of_succ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const bool test_eq_true = are_equal(
      (((((0 + 1) + 1) + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const bool test_eq_false = are_equal(
      (((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
};
