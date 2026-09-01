#include "empty_inductive_decimal_uint.h"

Uint Little::succ(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::d1(Uint::nil());
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d1(*a0);
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d2(*a0);
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d3(*a0);
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d4(*a0);
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d5(*a0);
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::d6(*a0);
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::d7(*a0);
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::d8(*a0);
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d9(*a0);
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d0(succ(*a0));
  }
}

String NilEmpty::string_of_uint(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return String::emptystring();
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return String::string0(Ascii::ascii0(Bool0::FALSE_, Bool0::FALSE_,
                                         Bool0::FALSE_, Bool0::FALSE_,
                                         Bool0::TRUE_, Bool0::TRUE_,
                                         Bool0::FALSE_, Bool0::FALSE_),
                           string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::FALSE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::FALSE_, Bool0::FALSE_, Bool0::TRUE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::TRUE_, Bool0::FALSE_, Bool0::TRUE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::FALSE_, Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::TRUE_, Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::FALSE_, Bool0::FALSE_, Bool0::FALSE_, Bool0::TRUE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return String::string0(
        Ascii::ascii0(Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_, Bool0::TRUE_,
                      Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),
        string_of_uint(*a0));
  }
}

String NilZero::string_of_uint(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return String::string0(Ascii::ascii0(Bool0::FALSE_, Bool0::FALSE_,
                                         Bool0::FALSE_, Bool0::FALSE_,
                                         Bool0::TRUE_, Bool0::TRUE_,
                                         Bool0::FALSE_, Bool0::FALSE_),
                           String::emptystring());
  } else {
    return NilEmpty::string_of_uint(d);
  }
}

String EmptyInductiveDecimalUint::s(const Nat::nat &n) {
  return NilZero::string_of_uint(Nat::to_uint(n));
}

Uint Nat::to_little_uint(const Nat::nat &n, Uint acc) {
  if (std::holds_alternative<typename Nat::nat::O>(n.v())) {
    return acc;
  } else {
    const auto &[a0] = std::get<typename Nat::nat::S>(n.v());
    return Nat::to_little_uint(*a0, Little::succ(std::move(acc)));
  }
}

Uint Nat::to_uint(const Nat::nat &n) {
  return Nat::to_little_uint(n, Uint::d0(Uint::nil())).rev();
}
