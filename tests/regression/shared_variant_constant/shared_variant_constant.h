#ifndef INCLUDED_SHARED_VARIANT_CONSTANT
#define INCLUDED_SHARED_VARIANT_CONSTANT

#include "crane_variant.h"
#include "shared_variant.h"
#include <cstdint>
#include <utility>
#include <variant>

struct Positive;

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
};

struct Positive {
  // TYPES
  struct XI {
    crane::shared_box<Positive> a0;

    // MANIPULATORS
    template <typename F> inline void crane_each_field(F &&_f) { _f(a0); }
  };

  struct XO {
    crane::shared_box<Positive> a0;

    // MANIPULATORS
    template <typename F> inline void crane_each_field(F &&_f) { _f(a0); }
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
};

#endif // INCLUDED_SHARED_VARIANT_CONSTANT
