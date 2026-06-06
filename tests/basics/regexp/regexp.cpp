#include "regexp.h"

bool Matcher::char_eq(int64_t x, int64_t y) {
  bool b = x == y;
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool Matcher::regexp_eq(const Matcher::regexp &r, const Matcher::regexp &x) {
  if (std::holds_alternative<typename Matcher::regexp::Any>(r.v())) {
    if (std::holds_alternative<typename Matcher::regexp::Any>(x.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Char>(r.v())) {
    const auto &[c0] = std::get<typename Matcher::regexp::Char>(r.v());
    if (std::holds_alternative<typename Matcher::regexp::Char>(x.v())) {
      const auto &[c2] = std::get<typename Matcher::regexp::Char>(x.v());
      if (char_eq(c0, c2)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Eps>(r.v())) {
    if (std::holds_alternative<typename Matcher::regexp::Eps>(x.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Cat>(r.v());
    if (std::holds_alternative<typename Matcher::regexp::Cat>(x.v())) {
      const auto &[r10, r20] = std::get<typename Matcher::regexp::Cat>(x.v());
      if (regexp_eq(*r4, *r10)) {
        if (regexp_eq(*r5, *r20)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Alt>(r.v());
    if (std::holds_alternative<typename Matcher::regexp::Alt>(x.v())) {
      const auto &[r10, r20] = std::get<typename Matcher::regexp::Alt>(x.v());
      if (regexp_eq(*r4, *r10)) {
        if (regexp_eq(*r5, *r20)) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Zero>(r.v())) {
    if (std::holds_alternative<typename Matcher::regexp::Zero>(x.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[r2] = std::get<typename Matcher::regexp::Star>(r.v());
    if (std::holds_alternative<typename Matcher::regexp::Star>(x.v())) {
      const auto &[r4] = std::get<typename Matcher::regexp::Star>(x.v());
      if (regexp_eq(*r2, *r4)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
}

/// An optimized constructor for Cat.
Matcher::regexp Matcher::OptCat(Matcher::regexp r2, Matcher::regexp r3) {
  if (std::holds_alternative<typename Matcher::regexp::Eps>(r2.v_mut())) {
    return r3;
  } else if (std::holds_alternative<typename Matcher::regexp::Zero>(
                 r2.v_mut())) {
    return regexp::zero();
  } else {
    if (std::holds_alternative<typename Matcher::regexp::Eps>(r3.v_mut())) {
      return r2;
    } else if (std::holds_alternative<typename Matcher::regexp::Zero>(
                   r3.v_mut())) {
      return regexp::zero();
    } else {
      return regexp::cat(std::move(r2), std::move(r3));
    }
  }
}

/// Optimized version of Alt.
Matcher::regexp Matcher::OptAlt(Matcher::regexp r2, Matcher::regexp r3) {
  if (std::holds_alternative<typename Matcher::regexp::Zero>(r2.v_mut())) {
    return r3;
  } else {
    if (std::holds_alternative<typename Matcher::regexp::Zero>(r3.v_mut())) {
      return r2;
    } else {
      if (regexp_eq(r2, r3)) {
        return r2;
      } else {
        return regexp::alt(std::move(r2), std::move(r3));
      }
    }
  }
}

/// If r accepts the empty string, return Eps, else return Zero.
Matcher::regexp Matcher::null(const Matcher::regexp &r) {
  if (std::holds_alternative<typename Matcher::regexp::Eps>(r.v())) {
    return regexp::eps();
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Cat>(r.v());
    return OptCat(null(*r4), null(*r5));
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Alt>(r.v());
    return OptAlt(null(*r4), null(*r5));
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r.v())) {
    return regexp::eps();
  } else {
    return regexp::zero();
  }
}

bool Matcher::accepts_null(const Matcher::regexp &r) {
  return regexp_eq(null(r), regexp::eps());
}

/// This is the heart of the algorithm.  It returns a regexp denoting
/// { cs | (c::cs) in r }.
Matcher::regexp Matcher::deriv(const Matcher::regexp &r, int64_t c) {
  if (std::holds_alternative<typename Matcher::regexp::Any>(r.v())) {
    return regexp::eps();
  } else if (std::holds_alternative<typename Matcher::regexp::Char>(r.v())) {
    const auto &[c0] = std::get<typename Matcher::regexp::Char>(r.v());
    if (char_eq(c, c0)) {
      return regexp::eps();
    } else {
      return regexp::zero();
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Cat>(r.v());
    return OptAlt(OptCat(deriv(*r4, c), *r5), OptCat(null(*r4), deriv(*r5, c)));
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Alt>(r.v());
    return OptAlt(deriv(*r4, c), deriv(*r5, c));
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r.v())) {
    const auto &[r2] = std::get<typename Matcher::regexp::Star>(r.v());
    return OptCat(deriv(*r2, c), regexp::star(*r2));
  } else {
    return regexp::zero();
  }
}

/// This calculates the derivative of a regular expression with respect to a
/// string.
Matcher::regexp Matcher::derivs(Matcher::regexp r, const List<int64_t> &cs) {
  if (std::holds_alternative<typename List<int64_t>::Nil>(cs.v())) {
    return r;
  } else {
    const auto &[a0, a1] = std::get<typename List<int64_t>::Cons>(cs.v());
    return derivs(deriv(std::move(r), a0), *a1);
  }
}

/// To see if cs matches r, calculate the derivative of r with respect
/// to s, and see if the resulting regexp accepts the empty string.
bool Matcher::deriv_parse(const Matcher::regexp &r, const List<int64_t> &cs) {
  if (accepts_null(derivs(r, cs))) {
    return true;
  } else {
    return false;
  }
}

/// null r returns Eps or Zero
bool Matcher::NullEpsOrZero(const Matcher::regexp &r) {
  if (std::holds_alternative<typename Matcher::regexp::Eps>(r.v())) {
    return true;
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Cat>(r.v());
    if (NullEpsOrZero(*r4)) {
      if (NullEpsOrZero(*r5)) {
        return true;
      } else {
        return false;
      }
    } else {
      if (NullEpsOrZero(*r5)) {
        return false;
      } else {
        return false;
      }
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r.v())) {
    const auto &[r4, r5] = std::get<typename Matcher::regexp::Alt>(r.v());
    if (NullEpsOrZero(*r4)) {
      if (NullEpsOrZero(*r5)) {
        return true;
      } else {
        return true;
      }
    } else {
      if (NullEpsOrZero(*r5)) {
        return true;
      } else {
        return false;
      }
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r.v())) {
    return true;
  } else {
    return false;
  }
}

/// From this, we can build a decidable regexp matcher by running
/// the derivative-based parser.
bool Matcher::parse(const Matcher::regexp &r, const List<int64_t> &cs) {
  bool b = deriv_parse(r, cs);
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool Matcher::parse_bool(const Matcher::regexp &r, const List<int64_t> &cs) {
  if (parse(r, cs)) {
    return true;
  } else {
    return false;
  }
}
