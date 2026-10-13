#ifndef INCLUDED_NUMBER
#define INCLUDED_NUMBER

#include <atomic>
#include <utility>
#include <variant>

#include "Datatypes.h"
#include "Decimal.h"
#include "Hexadecimal.h"
#include "Specif.h"

namespace Number {

struct Uint;
struct Signed_int;
struct Number;

struct Uint {
  // TYPES
  struct UIntDecimal {
    Decimal::Uint u;
  };

  struct UIntHexadecimal {
    Hexadecimal::Uint u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(UIntDecimal _v) : v_(std::move(_v)) {}

  explicit Uint(UIntHexadecimal _v) : v_(std::move(_v)) {}

  static Uint uintdecimal(Decimal::Uint u) {
    return Uint(UIntDecimal{std::move(u)});
  }

  static Uint uinthexadecimal(Hexadecimal::Uint u) {
    return Uint(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool uint_beq(const Uint &y) const {
    if (std::holds_alternative<typename Uint::UIntDecimal>(this->v())) {
      const auto &[u0] = std::get<typename Uint::UIntDecimal>(this->v());
      if (std::holds_alternative<typename Uint::UIntDecimal>(y.v())) {
        const auto &[u2] = std::get<typename Uint::UIntDecimal>(y.v());
        return u0.uint_beq(u2);
      } else {
        return false;
      }
    } else {
      const auto &[u0] = std::get<typename Uint::UIntHexadecimal>(this->v());
      if (std::holds_alternative<typename Uint::UIntDecimal>(y.v())) {
        return false;
      } else {
        const auto &[u2] = std::get<typename Uint::UIntHexadecimal>(y.v());
        return u0.uint_beq(u2);
      }
    }
  }

  bool uint_eq_dec(const Uint &y) const {
    bool h;
    bool b = this->uint_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }

  Uint uint_of_uint() const { return std::move(*this); }
};

struct Signed_int {
  // TYPES
  struct IntDecimal {
    Decimal::Signed_int i;
  };

  struct IntHexadecimal {
    Hexadecimal::Signed_int i;
  };

  using variant_t = std::variant<IntDecimal, IntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Signed_int() {}

  explicit Signed_int(IntDecimal _v) : v_(std::move(_v)) {}

  explicit Signed_int(IntHexadecimal _v) : v_(std::move(_v)) {}

  static Signed_int intdecimal(Decimal::Signed_int i) {
    return Signed_int(IntDecimal{std::move(i)});
  }

  static Signed_int inthexadecimal(Hexadecimal::Signed_int i) {
    return Signed_int(IntHexadecimal{std::move(i)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool signed_int_beq(const Signed_int &y) const {
    if (std::holds_alternative<typename Signed_int::IntDecimal>(this->v())) {
      const auto &[i0] = std::get<typename Signed_int::IntDecimal>(this->v());
      if (std::holds_alternative<typename Signed_int::IntDecimal>(y.v())) {
        const auto &[i2] = std::get<typename Signed_int::IntDecimal>(y.v());
        return i0.signed_int_beq(i2);
      } else {
        return false;
      }
    } else {
      const auto &[i0] =
          std::get<typename Signed_int::IntHexadecimal>(this->v());
      if (std::holds_alternative<typename Signed_int::IntDecimal>(y.v())) {
        return false;
      } else {
        const auto &[i2] = std::get<typename Signed_int::IntHexadecimal>(y.v());
        return i0.signed_int_beq(i2);
      }
    }
  }

  bool signed_int_eq_dec(const Signed_int &y) const {
    bool h;
    bool b = this->signed_int_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }

  Signed_int int_of_int() const { return std::move(*this); }
};

struct Number {
  // TYPES
  struct Decimal {
    ::Decimal::Decimal d;
  };

  struct Hexadecimal {
    ::Hexadecimal::Hexadecimal h;
  };

  using variant_t = std::variant<Decimal, Hexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Number() {}

  explicit Number(Decimal _v) : v_(std::move(_v)) {}

  explicit Number(Hexadecimal _v) : v_(std::move(_v)) {}

  static Number decimal(::Decimal::Decimal d) {
    return Number(Decimal{std::move(d)});
  }

  static Number hexadecimal(::Hexadecimal::Hexadecimal h) {
    return Number(Hexadecimal{std::move(h)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool number_beq(const Number &y) const {
    if (std::holds_alternative<typename Number::Decimal>(this->v())) {
      const auto &[d0] = std::get<typename Number::Decimal>(this->v());
      if (std::holds_alternative<typename Number::Decimal>(y.v())) {
        const auto &[d2] = std::get<typename Number::Decimal>(y.v());
        return d0.decimal_beq(d2);
      } else {
        return false;
      }
    } else {
      const auto &[h0] = std::get<typename Number::Hexadecimal>(this->v());
      if (std::holds_alternative<typename Number::Decimal>(y.v())) {
        return false;
      } else {
        const auto &[h2] = std::get<typename Number::Hexadecimal>(y.v());
        return h0.hexadecimal_beq(h2);
      }
    }
  }

  bool number_eq_dec(const Number &y) const {
    bool h;
    bool b = this->number_beq(y);
    if (b) {
      h = true;
    } else {
      h = false;
    }
    if (h) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace Number

#endif // INCLUDED_NUMBER
