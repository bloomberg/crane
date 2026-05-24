#ifndef INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
#define INCLUDED_TODO_MONADIC_GLOBAL_ALIAS

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <utility>
#include <variant>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct TodoMonadicGlobalAlias {
  static Nat base();
  static Nat alias();
  static Nat rebound();
};

#endif // INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
