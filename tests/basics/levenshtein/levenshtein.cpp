#include <levenshtein.h>

__attribute__((pure)) Levenshtein::chain
Levenshtein::same_chain(const String &s) {
  if (std::holds_alternative<typename String::EmptyString>(s.v())) {
    return chain::empty();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename String::String0>(s.v());
    return chain::skip(d_a0, *(d_a1), *(d_a1), Nat::o(), same_chain(*(d_a1)));
  }
}

__attribute__((pure)) Levenshtein::chain
Levenshtein::inserts_chain(const String &s1, const String &s2) {
  if (std::holds_alternative<typename String::EmptyString>(s1.v())) {
    return _inserts_chain_F<Levenshtein::chain>(s2);
  } else {
    const auto &[d_a0, d_a1] = std::get<typename String::String0>(s1.v());
    return inserts_chain(*(d_a1), s2)
        .insert_chain(d_a0, s2, (*(d_a1)).append(s2), (*(d_a1)).length());
  }
}

__attribute__((pure)) Levenshtein::chain
Levenshtein::inserts_chain_empty(const String &s) {
  if (std::holds_alternative<typename String::EmptyString>(s.v())) {
    return chain::empty();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename String::String0>(s.v());
    return inserts_chain_empty(*(d_a1)).insert_chain(
        d_a0, String::emptystring(), *(d_a1), (*(d_a1)).length());
  }
}

__attribute__((pure)) Levenshtein::chain
Levenshtein::deletes_chain(const String &s1, const String &s2) {
  if (std::holds_alternative<typename String::EmptyString>(s1.v())) {
    return same_chain(s2);
  } else {
    const auto &[d_a0, d_a1] = std::get<typename String::String0>(s1.v());
    return deletes_chain(*(d_a1), s2)
        .delete_chain(d_a0, (*(d_a1)).append(s2), s2, (*(d_a1)).length());
  }
}

__attribute__((pure)) Levenshtein::chain
Levenshtein::deletes_chain_empty(const String &s) {
  if (std::holds_alternative<typename String::EmptyString>(s.v())) {
    return chain::empty();
  } else {
    const auto &[d_a0, d_a1] = std::get<typename String::String0>(s.v());
    return deletes_chain_empty(*(d_a1)).delete_chain(
        d_a0, *(d_a1), String::emptystring(), (*(d_a1)).length());
  }
}

__attribute__((pure)) Levenshtein::chain
Levenshtein::aux_both_empty(const String &, const String &) {
  return chain::empty();
}

__attribute__((pure)) SigT<Nat, Levenshtein::chain>
Levenshtein::levenshtein_chain(const String &s, String _x0) {
  std::function<SigT<Nat, Levenshtein::chain>(String)> levenshtein_chain1;
  levenshtein_chain1 = [&](String t) -> SigT<Nat, Levenshtein::chain> {
    if (std::holds_alternative<typename String::EmptyString>(s.v())) {
      if (std::holds_alternative<typename String::EmptyString>(t.v())) {
        return SigT<Nat, Levenshtein::chain>::existt(Nat::o(),
                                                     aux_both_empty(s, t));
      } else {
        return SigT<Nat, Levenshtein::chain>::existt(t.length(),
                                                     inserts_chain_empty(t));
      }
    } else {
      const auto &[d_a0, d_a1] = std::get<typename String::String0>(s.v());
      if (std::holds_alternative<typename String::EmptyString>(t.v())) {
        return SigT<Nat, Levenshtein::chain>::existt(
            s.length(), deletes_chain_empty(String::string0(d_a0, *(d_a1))));
      } else {
        const auto &[d_a00, d_a10] = std::get<typename String::String0>(t.v());
        switch (d_a0.ascii_dec(d_a00)) {
        case Sumbool::e_LEFT: {
          auto &&_sv1 = levenshtein_chain(*(d_a1), *(d_a10));
          const auto &[d_x1, d_a11] =
              std::get<typename SigT<Nat, Levenshtein::chain>::ExistT>(
                  _sv1.v());
          return SigT<Nat, Levenshtein::chain>::existt(
              d_x1,
              d_a11.aux_eq_char(s, t, d_a0, *(d_a1), d_a00, *(d_a10), d_x1));
        }
        case Sumbool::e_RIGHT: {
          auto &&_sv2 = levenshtein_chain1(*(d_a10));
          const auto &[d_x2, d_a12] =
              std::get<typename SigT<Nat, Levenshtein::chain>::ExistT>(
                  _sv2.v());
          auto &&_sv3 =
              levenshtein_chain(*(d_a1), String::string0(d_a00, *(d_a10)));
          const auto &[d_x3, d_a13] =
              std::get<typename SigT<Nat, Levenshtein::chain>::ExistT>(
                  _sv3.v());
          auto &&_sv4 = levenshtein_chain(*(d_a1), *(d_a10));
          const auto &[d_x4, d_a14] =
              std::get<typename SigT<Nat, Levenshtein::chain>::ExistT>(
                  _sv4.v());
          Levenshtein::chain r1_ =
              d_a12.aux_insert(s, t, d_a0, *(d_a1), d_a00, *(d_a10), d_x2);
          Levenshtein::chain r2_ =
              d_a13.aux_delete(s, t, d_a0, *(d_a1), d_a00, *(d_a10), d_x3);
          Levenshtein::chain r3_ =
              d_a14.aux_update(s, t, d_a0, *(d_a1), d_a00, *(d_a10), d_x4);
          return min3_app<SigT<Nat, Levenshtein::chain>>(
              SigT<Nat, Levenshtein::chain>::existt(Nat::s(d_x2), r1_),
              SigT<Nat, Levenshtein::chain>::existt(Nat::s(d_x3), r2_),
              SigT<Nat, Levenshtein::chain>::existt(Nat::s(d_x4), r3_),
              [](const auto &_x) { return _x.projT1(); });
        }
        default:
          std::unreachable();
        }
      }
    }
  };
  return levenshtein_chain1(_x0);
}

__attribute__((pure)) Nat Levenshtein::levenshtein_computed(const String &s,
                                                            const String &t) {
  return levenshtein_chain(s, t).projT1();
}

__attribute__((pure)) Nat Levenshtein::levenshtein(const String &_x0,
                                                   const String &_x1) {
  return levenshtein_computed(_x0, _x1);
}

__attribute__((pure)) Sumbool Bool::bool_dec(const Bool0 b1, const Bool0 b2) {
  switch (b1) {
  case Bool0::e_TRUE0: {
    switch (b2) {
    case Bool0::e_TRUE0: {
      return Sumbool::e_LEFT;
    }
    case Bool0::e_FALSE0: {
      return Sumbool::e_RIGHT;
    }
    default:
      std::unreachable();
    }
  }
  case Bool0::e_FALSE0: {
    switch (b2) {
    case Bool0::e_TRUE0: {
      return Sumbool::e_RIGHT;
    }
    case Bool0::e_FALSE0: {
      return Sumbool::e_LEFT;
    }
    default:
      std::unreachable();
    }
  }
  default:
    std::unreachable();
  }
}
