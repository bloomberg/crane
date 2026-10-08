#ifndef INCLUDED_SHARED_VARIANT_CONSTANT
#define INCLUDED_SHARED_VARIANT_CONSTANT

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_variant.h"
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Positive;

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (l ? crane::shared_box<List<A>>::make(
                                 crane_convert<List<A>>(*l))
                           : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Positive {
  // TYPES
  struct XI {
    crane::shared_box<Positive> a0;
  };

  struct XO {
    crane::shared_box<Positive> a0;
  };

  struct XH {};

  using variant_t = crane::shared_variant<XI, XO, XH>;

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
    return Positive(XI{crane::shared_box<Positive>::make(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{crane::shared_box<Positive>::make(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct SharedVariantConstant {
  static Positive seven(std::monostate _x);
  static std::pair<Positive, Positive> pair_of(std::monostate _x);
  static Positive add_ten(const Positive &p);
  static Positive sum_tens(uint64_t n, Positive acc);
  static inline const Positive result = sum_tens(UINT64_C(100), Positive::xh());
  /// 2^110: a constant nested deeper than a compiler parses, whose
  /// initialiser is split into bindings that run once.
  static Positive huge(std::monostate _x);
  /// A constant that is no numeral is named k; so is the parameter, read
  /// last -- and so moved -- where the constant is built.
  static std::pair<List<Positive>, List<Positive>>
  with_k(const List<Positive> &k);
};

#endif // INCLUDED_SHARED_VARIANT_CONSTANT
