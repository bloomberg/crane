#ifndef INCLUDED_NUMBER
#define INCLUDED_NUMBER

#include <atomic>
#include <utility>
#include <variant>

#include "Datatypes.h"
#include "Decimal.h"
#include "Hexadecimal.h"
#include "Specif.h"

struct Uint;
struct Signed_int;
struct Number;

struct Uint {
  // TYPES
  struct UIntDecimal {
    Decimal::uint u;
  };

  struct UIntHexadecimal {
    Hexadecimal::uint u;
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

  static uint uintdecimal(Decimal::uint u) {
    return uint(UIntDecimal{std::move(u)});
  }

  static uint uinthexadecimal(Hexadecimal::uint u) {
    return uint(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool uint_beq(const uint &y) const {
    if (std::holds_alternative<typename uint::UIntDecimal>(this->v())) {
      const auto &[u0] = std::get<typename uint::UIntDecimal>(this->v());
      if (std::holds_alternative<typename uint::UIntDecimal>(y.v())) {
        const auto &[u2] = std::get<typename uint::UIntDecimal>(y.v());
        return uint_beq(u0, u2);
      } else {
        return false;
      }
    } else {
      const auto &[u0] = std::get<typename uint::UIntHexadecimal>(this->v());
      if (std::holds_alternative<typename uint::UIntDecimal>(y.v())) {
        return false;
      } else {
        const auto &[u2] = std::get<typename uint::UIntHexadecimal>(y.v());
        return uint_beq(u0, u2);
      }
    }
  }

  bool uint_eq_dec(const uint &y) const {
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

  uint uint_of_uint() const { return std::move(*this); }
};

struct Signed_int {
  // TYPES
  struct IntDecimal {
    Decimal::signed_int i;
  };

  struct IntHexadecimal {
    Hexadecimal::signed_int i;
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

  static signed_int intdecimal(Decimal::signed_int i) {
    return signed_int(IntDecimal{std::move(i)});
  }

  static signed_int inthexadecimal(Hexadecimal::signed_int i) {
    return signed_int(IntHexadecimal{std::move(i)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool signed_int_beq(const signed_int &y) const {
    if (std::holds_alternative<typename signed_int::IntDecimal>(this->v())) {
      const auto &[i0] = std::get<typename signed_int::IntDecimal>(this->v());
      if (std::holds_alternative<typename signed_int::IntDecimal>(y.v())) {
        const auto &[i2] = std::get<typename signed_int::IntDecimal>(y.v());
        return signed_int_beq(i0, i2);
      } else {
        return false;
      }
    } else {
      const auto &[i0] =
          std::get<typename signed_int::IntHexadecimal>(this->v());
      if (std::holds_alternative<typename signed_int::IntDecimal>(y.v())) {
        return false;
      } else {
        const auto &[i2] = std::get<typename signed_int::IntHexadecimal>(y.v());
        return signed_int_beq(i0, i2);
      }
    }
  }

  bool signed_int_eq_dec(const signed_int &y) const {
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

  signed_int int_of_int() const { return std::move(*this); }
};

struct Number {
  // TYPES
  struct Decimal {
    Decimal::Decimal d;
  };

  struct Hexadecimal {
    Hexadecimal::Hexadecimal h;
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

  static number decimal(Decimal::Decimal d) {
    return number(Decimal{std::move(d)});
  }

  static number hexadecimal(Hexadecimal::Hexadecimal h) {
    return number(Hexadecimal{std::move(h)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool number_beq(const number &y) const {
    if (std::holds_alternative<typename number::Decimal>(this->v())) {
      const auto &[d0] = std::get<typename number::Decimal>(this->v());
      if (std::holds_alternative<typename number::Decimal>(y.v())) {
        const auto &[d2] = std::get<typename number::Decimal>(y.v());
        return decimal_beq(d0, d2);
      } else {
        return false;
      }
    } else {
      const auto &[h0] = std::get<typename number::Hexadecimal>(this->v());
      if (std::holds_alternative<typename number::Decimal>(y.v())) {
        return false;
      } else {
        const auto &[h2] = std::get<typename number::Hexadecimal>(y.v());
        return hexadecimal_beq(h0, h2);
      }
    }
  }

  bool number_eq_dec(const number &y) const {
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

#endif // INCLUDED_NUMBER
