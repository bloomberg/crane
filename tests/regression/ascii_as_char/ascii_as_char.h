#ifndef INCLUDED_ASCII_AS_CHAR
#define INCLUDED_ASCII_AS_CHAR

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
enum class Comparison;
struct Positive;
struct N;
struct String;

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);
};

struct Ascii0 {
  static N N_of_digits(const List<bool> &l);
  static N N_of_ascii(char a);
  static uint64_t nat_of_ascii(char a);
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Comparison { EQ, LT, GT };

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Positive> {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Positive> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    Positive a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : v_(_v) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

  static N n0() { return N(N0{}); }

  static N npos(Positive a0) { return N(Npos{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
};

struct BinNat {
  static N add(N n, N m);
  static N mul(const N &n, const N &m);
  static uint64_t to_nat(const N &a);
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    char a0;
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

  static String string0(char a0, String a1) {
    return String(String0{a0, std::make_shared<String>(std::move(a1))});
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
};

/// With Mapping.AsciiChar, a character is a C++ char: identifier
/// comparison compares bytes instead of building a binary natural per
/// character.  The constructor packs bits and a match unpacks them, so
/// code that looks inside a character still works.
struct AsciiAsChar {
  static Comparison cmp(const String &a, const String &b);
  static bool same(const String &a, const String &b);
  /// Looks inside a character: its low bit.
  static bool odd_code(char c);
  static bool decide(char a, char b);
  static bool check(std::monostate _x);
};

#endif // INCLUDED_ASCII_AS_CHAR
