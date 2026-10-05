#ifndef INCLUDED_LIFTED_INSTANCE_QUALIFIED
#define INCLUDED_LIFTED_INSTANCE_QUALIFIED

#include "crane_fn.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct showN;
struct Nat;
struct Ascii;
struct String;
template <typename I, typename T>
concept Show = requires {
  { I::show(std::declval<T>()) } -> std::convertible_to<String>;
  { I::name() } -> std::convertible_to<String>;
};

struct LiftedInstanceQualified {
  static String use(const Nat &n);
};

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
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const {
    std::optional<String> _root{};
    std::shared_ptr<String> *_write = nullptr;
    const String *_loop_self = this;
    String _loop_s2 = std::move(s2);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
        auto _value = std::move(_loop_s2);
        (_write ? *(*_write = std::make_shared<String>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
        auto _cell = typename String::String0(a0, nullptr);
        String &_node =
            (_write ? *(*_write = std::make_shared<String>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename String::String0>(_node.v_mut()).a1;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Other {
  static inline const String banner = String::string0(
      Ascii::ascii0(true, true, true, true, false, true, true, false),
      String::emptystring());
};

struct StringUtil {
  static inline const String banner0 = String::string0(
      Ascii::ascii0(true, false, true, false, true, true, true, false),
      String::emptystring());
};

struct showN {
  static String show(Nat) {
    return String::string0(
        Ascii::ascii0(false, true, true, true, false, true, true, false),
        String::emptystring());
  }

  static String name() {
    return String::string0(
        Ascii::ascii0(false, true, true, true, false, true, true, false),
        String::string0(
            Ascii::ascii0(true, false, false, false, false, true, true, false),
            String::string0(Ascii::ascii0(false, false, true, false, true, true,
                                          true, false),
                            String::emptystring())));
  }
};

static_assert(Show<showN, Nat>);

#endif // INCLUDED_LIFTED_INSTANCE_QUALIFIED
