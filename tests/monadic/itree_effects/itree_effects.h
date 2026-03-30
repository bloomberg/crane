#ifndef INCLUDED_ITREE_EFFECTS
#define INCLUDED_ITREE_EFFECTS

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  static std::unique_ptr<Nat> o_uptr() { return std::make_unique<Nat>(O{}); }

  static std::unique_ptr<Nat> s_uptr(const std::shared_ptr<Nat> &a0) {
    return std::make_unique<Nat>(S{a0});
  }

  static std::unique_ptr<Nat> s_uptr(std::shared_ptr<Nat> &&a0) {
    return std::make_unique<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

/// ------------------------------------------------------------------
struct ITreeEffects {
  static void greet();
  static void simple_log();
  static void simple_print();
  static std::shared_ptr<Nat> pure_value();
};

#endif // INCLUDED_ITREE_EFFECTS
