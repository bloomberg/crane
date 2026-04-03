#ifndef INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
#define INCLUDED_TODO_MONADIC_GLOBAL_ALIAS

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

struct TodoMonadicGlobalAlias {
  static std::shared_ptr<Nat> base();
  static std::shared_ptr<Nat> alias();
  static std::shared_ptr<Nat> rebound();
};

#endif // INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
