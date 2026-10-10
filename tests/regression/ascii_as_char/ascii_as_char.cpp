#include "ascii_as_char.h"

Positive Coq_Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(*a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

Positive Coq_Pos::add(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add(*a0, *a00));
    } else {
      return Positive::xi(*a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(succ(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(*a00);
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

Positive Coq_Pos::add_carry(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else {
      return Positive::xi(succ(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(add_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(add(*a0, *a00));
    } else {
      return Positive::xo(succ(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xi(succ(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xo(succ(*a00));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

Positive Coq_Pos::mul(const Positive &x, Positive y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return add(y, Positive::xo(mul(*a0, y)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xo(mul(*a0, std::move(y)));
  } else {
    return y;
  }
}

uint64_t Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, x,
      UINT64_C(1));
}

N BinNat::add(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return m;
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return n;
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return N::npos(Coq_Pos::add(a0, a00));
    }
  }
}

N BinNat::mul(const N &n, const N &m) {
  if (std::holds_alternative<typename N::N0>(n.v())) {
    return N::n0();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(n.v());
    if (std::holds_alternative<typename N::N0>(m.v())) {
      return N::n0();
    } else {
      const auto &[a00] = std::get<typename N::Npos>(m.v());
      return N::npos(Coq_Pos::mul(a0, a00));
    }
  }
}

uint64_t BinNat::to_nat(const N &a) {
  if (std::holds_alternative<typename N::N0>(a.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename N::Npos>(a.v());
    return Pos::to_nat(a0);
  }
}

/// With Mapping.AsciiChar, a character is a C++ char: identifier
/// comparison compares bytes instead of building a binary natural per
/// character.  The constructor packs bits and a match unpacks them, so
/// code that looks inside a character still works.
Comparison AsciiAsChar::cmp(const String &a, const String &b) {
  if (std::holds_alternative<typename String::EmptyString>(a.v())) {
    if (std::holds_alternative<typename String::EmptyString>(b.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0, a1] = std::get<typename String::String0>(a.v());
    if (std::holds_alternative<typename String::EmptyString>(b.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00, a10] = std::get<typename String::String0>(b.v());
      switch ([](char _x, char _y) {
        return static_cast<Comparison>(
            _x == _y ? 0
                     : (static_cast<unsigned char>(_x) <
                                static_cast<unsigned char>(_y)
                            ? 1
                            : 2));
      }(a0, a00)) {
      case Comparison::EQ: {
        return cmp(*a1, *a10);
      }
      case Comparison::LT: {
        return Comparison::LT;
      }
      case Comparison::GT: {
        return Comparison::GT;
      }
      default:
        std::unreachable();
      }
    }
  }
}

bool AsciiAsChar::same(const String &a, const String &b) {
  if (std::holds_alternative<typename String::EmptyString>(a.v())) {
    if (std::holds_alternative<typename String::EmptyString>(b.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0, a1] = std::get<typename String::String0>(a.v());
    if (std::holds_alternative<typename String::EmptyString>(b.v())) {
      return false;
    } else {
      const auto &[a00, a10] = std::get<typename String::String0>(b.v());
      return (std::equal_to<char>{}(a0, a00) && same(*a1, *a10));
    }
  }
}

/// Looks inside a character: its low bit.
bool AsciiAsChar::odd_code(char c) {
  const bool b0 = (static_cast<unsigned char>(c) & 1) != 0;
  const bool _x = (static_cast<unsigned char>(c) & 2) != 0;
  const bool _x0 = (static_cast<unsigned char>(c) & 4) != 0;
  const bool _x1 = (static_cast<unsigned char>(c) & 8) != 0;
  const bool _x2 = (static_cast<unsigned char>(c) & 16) != 0;
  const bool _x3 = (static_cast<unsigned char>(c) & 32) != 0;
  const bool _x4 = (static_cast<unsigned char>(c) & 64) != 0;
  const bool _x5 = (static_cast<unsigned char>(c) & 128) != 0;
  return b0;
}

bool AsciiAsChar::decide(char a, char b) {
  if (std::equal_to<char>{}(a, b)) {
    return true;
  } else {
    return false;
  }
}

bool AsciiAsChar::check(std::monostate) {
  switch (cmp(
      String::string0(
          static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) | (true ? 4 : 0) |
                            (true ? 8 : 0) | (false ? 16 : 0) |
                            (true ? 32 : 0) | (true ? 64 : 0) |
                            (false ? 128 : 0)),
          String::string0(
              static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                (true ? 4 : 0) | (true ? 8 : 0) |
                                (false ? 16 : 0) | (true ? 32 : 0) |
                                (true ? 64 : 0) | (false ? 128 : 0)),
              String::string0(
                  static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                    (false ? 4 : 0) | (false ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)),
                  String::string0(
                      static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                        (true ? 4 : 0) | (false ? 8 : 0) |
                                        (false ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)),
                      String::emptystring())))),
      String::string0(
          static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) | (true ? 4 : 0) |
                            (true ? 8 : 0) | (false ? 16 : 0) |
                            (true ? 32 : 0) | (true ? 64 : 0) |
                            (false ? 128 : 0)),
          String::string0(
              static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                (true ? 4 : 0) | (true ? 8 : 0) |
                                (false ? 16 : 0) | (true ? 32 : 0) |
                                (true ? 64 : 0) | (false ? 128 : 0)),
              String::string0(
                  static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                    (true ? 4 : 0) | (true ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)),
                  String::string0(
                      static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                        (false ? 4 : 0) | (false ? 8 : 0) |
                                        (true ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)),
                      String::emptystring())))))) {
  case Comparison::LT: {
    switch (cmp(
        String::string0(
            static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                              (false ? 4 : 0) | (false ? 8 : 0) |
                              (true ? 16 : 0) | (true ? 32 : 0) |
                              (true ? 64 : 0) | (false ? 128 : 0)),
            String::string0(
                static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                  (true ? 4 : 0) | (false ? 8 : 0) |
                                  (true ? 16 : 0) | (true ? 32 : 0) |
                                  (true ? 64 : 0) | (false ? 128 : 0)),
                String::string0(
                    static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                      (true ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)),
                    String::string0(
                        static_cast<char>((false ? 1 : 0) | (true ? 2 : 0) |
                                          (false ? 4 : 0) | (false ? 8 : 0) |
                                          (true ? 16 : 0) | (true ? 32 : 0) |
                                          (true ? 64 : 0) | (false ? 128 : 0)),
                        String::string0(static_cast<char>(
                                            (true ? 1 : 0) | (false ? 2 : 0) |
                                            (true ? 4 : 0) | (false ? 8 : 0) |
                                            (false ? 16 : 0) | (true ? 32 : 0) |
                                            (true ? 64 : 0) |
                                            (false ? 128 : 0)),
                                        String::emptystring()))))),
        String::string0(
            static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                              (false ? 4 : 0) | (false ? 8 : 0) |
                              (true ? 16 : 0) | (true ? 32 : 0) |
                              (true ? 64 : 0) | (false ? 128 : 0)),
            String::string0(
                static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                  (true ? 4 : 0) | (false ? 8 : 0) |
                                  (true ? 16 : 0) | (true ? 32 : 0) |
                                  (true ? 64 : 0) | (false ? 128 : 0)),
                String::string0(
                    static_cast<char>((true ? 1 : 0) | (true ? 2 : 0) |
                                      (true ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)),
                    String::string0(
                        static_cast<char>((false ? 1 : 0) | (true ? 2 : 0) |
                                          (false ? 4 : 0) | (false ? 8 : 0) |
                                          (true ? 16 : 0) | (true ? 32 : 0) |
                                          (true ? 64 : 0) | (false ? 128 : 0)),
                        String::string0(static_cast<char>(
                                            (true ? 1 : 0) | (false ? 2 : 0) |
                                            (true ? 4 : 0) | (false ? 8 : 0) |
                                            (false ? 16 : 0) | (true ? 32 : 0) |
                                            (true ? 64 : 0) |
                                            (false ? 128 : 0)),
                                        String::emptystring()))))))) {
    case Comparison::EQ: {
      switch (cmp(
          String::string0(
              static_cast<char>((false ? 1 : 0) | (true ? 2 : 0) |
                                (false ? 4 : 0) | (true ? 8 : 0) |
                                (true ? 16 : 0) | (true ? 32 : 0) |
                                (true ? 64 : 0) | (false ? 128 : 0)),
              String::string0(
                  static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                    (true ? 4 : 0) | (false ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)),
                  String::string0(
                      static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                        (false ? 4 : 0) | (true ? 8 : 0) |
                                        (true ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)),
                      String::string0(static_cast<char>(
                                          (false ? 1 : 0) | (false ? 2 : 0) |
                                          (true ? 4 : 0) | (false ? 8 : 0) |
                                          (true ? 16 : 0) | (true ? 32 : 0) |
                                          (true ? 64 : 0) | (false ? 128 : 0)),
                                      String::emptystring())))),
          String::string0(
              static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                (false ? 4 : 0) | (false ? 8 : 0) |
                                (false ? 16 : 0) | (true ? 32 : 0) |
                                (true ? 64 : 0) | (false ? 128 : 0)),
              String::string0(
                  static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                    (true ? 4 : 0) | (false ? 8 : 0) |
                                    (false ? 16 : 0) | (true ? 32 : 0) |
                                    (true ? 64 : 0) | (false ? 128 : 0)),
                  String::string0(
                      static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                        (true ? 4 : 0) | (false ? 8 : 0) |
                                        (false ? 16 : 0) | (true ? 32 : 0) |
                                        (true ? 64 : 0) | (false ? 128 : 0)),
                      String::emptystring()))))) {
      case Comparison::GT: {
        return ((((((same(String::string0(
                              static_cast<char>(
                                  (false ? 1 : 0) | (false ? 2 : 0) |
                                  (false ? 4 : 0) | (false ? 8 : 0) |
                                  (true ? 16 : 0) | (true ? 32 : 0) |
                                  (true ? 64 : 0) | (false ? 128 : 0)),
                              String::string0(
                                  static_cast<char>(
                                      (false ? 1 : 0) | (false ? 2 : 0) |
                                      (false ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)),
                                  String::string0(
                                      static_cast<char>(
                                          (true ? 1 : 0) | (false ? 2 : 0) |
                                          (false ? 4 : 0) | (true ? 8 : 0) |
                                          (false ? 16 : 0) | (true ? 32 : 0) |
                                          (true ? 64 : 0) | (false ? 128 : 0)),
                                      String::emptystring()))),
                          String::string0(
                              static_cast<char>(
                                  (false ? 1 : 0) | (false ? 2 : 0) |
                                  (false ? 4 : 0) | (false ? 8 : 0) |
                                  (true ? 16 : 0) | (true ? 32 : 0) |
                                  (true ? 64 : 0) | (false ? 128 : 0)),
                              String::string0(
                                  static_cast<char>(
                                      (false ? 1 : 0) | (false ? 2 : 0) |
                                      (false ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)),
                                  String::string0(
                                      static_cast<char>(
                                          (true ? 1 : 0) | (false ? 2 : 0) |
                                          (false ? 4 : 0) | (true ? 8 : 0) |
                                          (false ? 16 : 0) | (true ? 32 : 0) |
                                          (true ? 64 : 0) | (false ? 128 : 0)),
                                      String::emptystring())))) &&
                     !(same(
                         String::string0(
                             static_cast<char>(
                                 (false ? 1 : 0) | (false ? 2 : 0) |
                                 (false ? 4 : 0) | (false ? 8 : 0) |
                                 (true ? 16 : 0) | (true ? 32 : 0) |
                                 (true ? 64 : 0) | (false ? 128 : 0)),
                             String::string0(
                                 static_cast<char>(
                                     (false ? 1 : 0) | (false ? 2 : 0) |
                                     (false ? 4 : 0) | (true ? 8 : 0) |
                                     (false ? 16 : 0) | (true ? 32 : 0) |
                                     (true ? 64 : 0) | (false ? 128 : 0)),
                                 String::string0(
                                     static_cast<char>(
                                         (true ? 1 : 0) |
                                         (false ? 2 : 0) | (false ? 4 : 0) |
                                         (true ? 8 : 0) | (false ? 16 : 0) |
                                         (true ? 32 : 0) | (true ? 64 : 0) |
                                         (false ? 128 : 0)),
                                     String::emptystring()))),
                         String::string0(
                             static_cast<char>(
                                 (false ? 1 : 0) | (false ? 2 : 0) |
                                 (false ? 4 : 0) | (false ? 8 : 0) |
                                 (true ? 16 : 0) | (true ? 32 : 0) |
                                 (true ? 64 : 0) | (false ? 128 : 0)),
                             String::string0(
                                 static_cast<char>(
                                     (false ? 1 : 0) | (false ? 2 : 0) |
                                     (false ? 4 : 0) | (true ? 8 : 0) |
                                     (false ? 16 : 0) | (true ? 32 : 0) |
                                     (true ? 64 : 0) | (false ? 128 : 0)),
                                 String::string0(
                                     static_cast<char>(
                                         (false ? 1 : 0) | (true ? 2 : 0) |
                                         (false ? 4 : 0) | (true ? 8 : 0) |
                                         (false ? 16 : 0) | (true ? 32 : 0) |
                                         (true ? 64 : 0) | (false ? 128 : 0)),
                                     String::emptystring())))))) &&
                    odd_code(static_cast<char>(
                        (true ? 1 : 0) | (false ? 2 : 0) | (false ? 4 : 0) |
                        (false ? 8 : 0) | (false ? 16 : 0) | (true ? 32 : 0) |
                        (true ? 64 : 0) | (false ? 128 : 0)))) &&
                   !(odd_code(static_cast<char>(
                       (false ? 1 : 0) | (true ? 2 : 0) | (false ? 4 : 0) |
                       (false ? 8 : 0) | (false ? 16 : 0) | (true ? 32 : 0) |
                       (true ? 64 : 0) | (false ? 128 : 0))))) &&
                  decide(static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                           (false ? 4 : 0) | (true ? 8 : 0) |
                                           (true ? 16 : 0) | (true ? 32 : 0) |
                                           (true ? 64 : 0) | (false ? 128 : 0)),
                         static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                           (false ? 4 : 0) | (true ? 8 : 0) |
                                           (true ? 16 : 0) | (true ? 32 : 0) |
                                           (true ? 64 : 0) |
                                           (false ? 128 : 0)))) &&
                 !(decide(
                     static_cast<char>((false ? 1 : 0) | (false ? 2 : 0) |
                                       (false ? 4 : 0) | (true ? 8 : 0) |
                                       (true ? 16 : 0) | (true ? 32 : 0) |
                                       (true ? 64 : 0) | (false ? 128 : 0)),
                     static_cast<char>(
                         (true ? 1 : 0) | (false ? 2 : 0) | (false ? 4 : 0) |
                         (true ? 8 : 0) | (true ? 16 : 0) | (true ? 32 : 0) |
                         (true ? 64 : 0) | (false ? 128 : 0))))) &&
                Ascii0::nat_of_ascii(static_cast<char>(
                    (true ? 1 : 0) | (false ? 2 : 0) | (false ? 4 : 0) |
                    (false ? 8 : 0) | (false ? 16 : 0) | (false ? 32 : 0) |
                    (true ? 64 : 0) | (false ? 128 : 0))) == UINT64_C(65));
      }
      default: {
        return false;
      }
      }
      break;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default: {
    return false;
  }
  }
}

N Ascii0::N_of_digits(const List<bool> &l) {
  if (std::holds_alternative<typename List<bool>::Nil>(l.v())) {
    return N::n0();
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(l.v());
    return BinNat::add((a0 ? N::npos(Positive::xh()) : N::n0()),
                       BinNat::mul(N::npos(Positive::xo(Positive::xh())),
                                   Ascii0::N_of_digits(*a1)));
  }
}

N Ascii0::N_of_ascii(char a) {
  const bool a0 = (static_cast<unsigned char>(a) & 1) != 0;
  const bool a1 = (static_cast<unsigned char>(a) & 2) != 0;
  const bool a2 = (static_cast<unsigned char>(a) & 4) != 0;
  const bool a3 = (static_cast<unsigned char>(a) & 8) != 0;
  const bool a4 = (static_cast<unsigned char>(a) & 16) != 0;
  const bool a5 = (static_cast<unsigned char>(a) & 32) != 0;
  const bool a6 = (static_cast<unsigned char>(a) & 64) != 0;
  const bool a7 = (static_cast<unsigned char>(a) & 128) != 0;
  return Ascii0::N_of_digits(List<bool>::cons(
      a0,
      List<bool>::cons(
          a1,
          List<bool>::cons(
              a2,
              List<bool>::cons(
                  a3,
                  List<bool>::cons(
                      a4, List<bool>::cons(
                              a5, List<bool>::cons(
                                      a6, List<bool>::cons(
                                              a7, List<bool>::nil())))))))));
}

uint64_t Ascii0::nat_of_ascii(char a) {
  return BinNat::to_nat(Ascii0::N_of_ascii(a));
}
