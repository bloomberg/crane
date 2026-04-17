#ifndef INCLUDED_FUNCTION_RETURN_BRANCH_PROBE
#define INCLUDED_FUNCTION_RETURN_BRANCH_PROBE

#include <functional>
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

struct FunctionReturnBranchProbe {
  /// A recursive function whose match branches return different lambda
  /// expressions.  Crane generates an inner lambda with no explicit return
  /// type, causing C++ to fail to deduce a common return type across the two
  /// distinct closure types.
  static std::shared_ptr<Nat> make_adder(const std::shared_ptr<Nat> &n,
                                         const std::shared_ptr<Nat> &_x0);
  static inline const std::shared_ptr<Nat> sample = make_adder(
      Nat::s(Nat::s(Nat::o())),
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::o())))))))))))))))))))))))))))))))))))))))));
};

#endif // INCLUDED_FUNCTION_RETURN_BRANCH_PROBE
