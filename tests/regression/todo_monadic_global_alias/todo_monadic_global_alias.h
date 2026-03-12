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

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> _a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Nat(O _v) : v_(std::move(_v)) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct TodoMonadicGlobalAlias {
  static std::shared_ptr<Nat> base();
  static std::shared_ptr<Nat> alias();
  static std::shared_ptr<Nat> rebound();
};
