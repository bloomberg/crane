#include "ascii_char_without_bool_mapping.h"

Positive Coq_Pos::succ(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xo(succ(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(crane::shared_child(a0));
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
      return Positive::xi(crane::shared_child(a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return Positive::xo(succ(*a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return Positive::xi(crane::shared_child(a00));
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

Nat Pos::to_nat(const Positive &x) {
  return iter_op<Nat>(
      [](const Nat &_x0, const Nat &_x1) { return _x0.add(_x1); }, x,
      Nat::s(Nat::o()));
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

Nat BinNat::to_nat(const N &a) {
  if (std::holds_alternative<typename N::N0>(a.v())) {
    return Nat::o();
  } else {
    const auto &[a0] = std::get<typename N::Npos>(a.v());
    return Pos::to_nat(a0);
  }
}

N Ascii0::N_of_digits(const List<Bool0> &l) {
  if (std::holds_alternative<typename List<Bool0>::Nil>(l.v())) {
    return N::n0();
  } else {
    const auto &[a0, a1] = std::get<typename List<Bool0>::Cons>(l.v());
    return BinNat::add(
        [&]() {
          switch (a0) {
          case Bool0::TRUE_: {
            return N::npos(Positive::xh());
          }
          case Bool0::FALSE_: {
            return N::n0();
          }
          default:
            std::unreachable();
          }
        }(),
        BinNat::mul(N::npos(Positive::xo(Positive::xh())),
                    Ascii0::N_of_digits(*a1)));
  }
}

N Ascii0::N_of_ascii(char a) {
  auto a0 = (static_cast<unsigned char>(a) & 1) != 0;
  auto a1 = (static_cast<unsigned char>(a) & 2) != 0;
  auto a2 = (static_cast<unsigned char>(a) & 4) != 0;
  auto a3 = (static_cast<unsigned char>(a) & 8) != 0;
  auto a4 = (static_cast<unsigned char>(a) & 16) != 0;
  auto a5 = (static_cast<unsigned char>(a) & 32) != 0;
  auto a6 = (static_cast<unsigned char>(a) & 64) != 0;
  auto a7 = (static_cast<unsigned char>(a) & 128) != 0;
  return Ascii0::N_of_digits(List<Bool0>::cons(
      a0,
      List<Bool0>::cons(
          a1,
          List<Bool0>::cons(
              a2,
              List<Bool0>::cons(
                  a3, List<Bool0>::cons(
                          a4, List<Bool0>::cons(
                                  a5, List<Bool0>::cons(
                                          a6, List<Bool0>::cons(
                                                  a7,
                                                  List<Bool0>::nil())))))))));
}

Nat Ascii0::nat_of_ascii(char a) {
  return BinNat::to_nat(Ascii0::N_of_ascii(a));
}
