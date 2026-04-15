#include <regexp.h>

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool Matcher::char_eq(const int64_t x, const int64_t y) {
  bool b = x == y;
  if (b) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
Matcher::regexp_eq(const std::shared_ptr<Matcher::regexp> &r,
                   const std::shared_ptr<Matcher::regexp> &x) {
  if (std::holds_alternative<typename Matcher::regexp::Any>(r->v())) {
    if (std::holds_alternative<typename Matcher::regexp::Any>(x->v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Char>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Char>(&r->v());
    if (std::holds_alternative<typename Matcher::regexp::Char>(x->v())) {
      const auto &_m0 = *std::get_if<typename Matcher::regexp::Char>(&x->v());
      if (char_eq(_m.d_c, _m0.d_c)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Eps>(r->v())) {
    if (std::holds_alternative<typename Matcher::regexp::Eps>(x->v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Cat>(&r->v());
    if (std::holds_alternative<typename Matcher::regexp::Cat>(x->v())) {
      const auto &_m0 = *std::get_if<typename Matcher::regexp::Cat>(&x->v());
      if (regexp_eq(_m.d_r1, _m0.d_r1)) {
        if (regexp_eq(_m.d_r2, _m0.d_r2)) {
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
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Alt>(&r->v());
    if (std::holds_alternative<typename Matcher::regexp::Alt>(x->v())) {
      const auto &_m0 = *std::get_if<typename Matcher::regexp::Alt>(&x->v());
      if (regexp_eq(_m.d_r1, _m0.d_r1)) {
        if (regexp_eq(_m.d_r2, _m0.d_r2)) {
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
  } else if (std::holds_alternative<typename Matcher::regexp::Zero>(r->v())) {
    if (std::holds_alternative<typename Matcher::regexp::Zero>(x->v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &_m = *std::get_if<typename Matcher::regexp::Star>(&r->v());
    if (std::holds_alternative<typename Matcher::regexp::Star>(x->v())) {
      const auto &_m0 = *std::get_if<typename Matcher::regexp::Star>(&x->v());
      if (regexp_eq(_m.d_r, _m0.d_r)) {
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
std::shared_ptr<Matcher::regexp>
Matcher::OptCat(std::shared_ptr<Matcher::regexp> r2,
                std::shared_ptr<Matcher::regexp> r3) {
  if (std::holds_alternative<typename Matcher::regexp::Zero>(r2->v()) &&
      r2.use_count() == 1) {
    return r2;
  } else if (std::holds_alternative<typename Matcher::regexp::Eps>(r2->v())) {
    return r3;
  } else if (std::holds_alternative<typename Matcher::regexp::Zero>(r2->v())) {
    return regexp::zero();
  } else {
    if (std::holds_alternative<typename Matcher::regexp::Zero>(r3->v()) &&
        r3.use_count() == 1) {
      return r3;
    } else if (std::holds_alternative<typename Matcher::regexp::Eps>(r3->v())) {
      return r2;
    } else if (std::holds_alternative<typename Matcher::regexp::Zero>(
                   r3->v())) {
      return regexp::zero();
    } else {
      return regexp::cat(r2, r3);
    }
  }
}

/// Optimized version of Alt.
std::shared_ptr<Matcher::regexp>
Matcher::OptAlt(std::shared_ptr<Matcher::regexp> r2,
                std::shared_ptr<Matcher::regexp> r3) {
  if (std::holds_alternative<typename Matcher::regexp::Zero>(r2->v())) {
    return r3;
  } else {
    if (std::holds_alternative<typename Matcher::regexp::Zero>(r3->v())) {
      return r2;
    } else {
      if (regexp_eq(r2, r3)) {
        return r2;
      } else {
        return regexp::alt(r2, r3);
      }
    }
  }
}

/// If r accepts the empty string, return Eps, else return Zero.
std::shared_ptr<Matcher::regexp>
Matcher::null(const std::shared_ptr<Matcher::regexp> &r) {
  if (std::holds_alternative<typename Matcher::regexp::Eps>(r->v())) {
    return regexp::eps();
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Cat>(&r->v());
    return OptCat(null(_m.d_r1), null(_m.d_r2));
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Alt>(&r->v());
    return OptAlt(null(_m.d_r1), null(_m.d_r2));
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r->v())) {
    return regexp::eps();
  } else {
    return regexp::zero();
  }
}

__attribute__((pure)) bool
Matcher::accepts_null(const std::shared_ptr<Matcher::regexp> &r) {
  return regexp_eq(null(r), regexp::eps());
}

/// This is the heart of the algorithm.  It returns a regexp denoting
/// { cs | (c::cs) in r }.
std::shared_ptr<Matcher::regexp>
Matcher::deriv(const std::shared_ptr<Matcher::regexp> &r, const int64_t c) {
  if (std::holds_alternative<typename Matcher::regexp::Any>(r->v())) {
    return regexp::eps();
  } else if (std::holds_alternative<typename Matcher::regexp::Char>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Char>(&r->v());
    if (char_eq(c, _m.d_c)) {
      return regexp::eps();
    } else {
      return regexp::zero();
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Cat>(&r->v());
    return OptAlt(OptCat(deriv(_m.d_r1, c), _m.d_r2),
                  OptCat(null(_m.d_r1), deriv(_m.d_r2, c)));
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Alt>(&r->v());
    return OptAlt(deriv(_m.d_r1, c), deriv(_m.d_r2, c));
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Star>(&r->v());
    return OptCat(deriv(_m.d_r, c), regexp::star(_m.d_r));
  } else {
    return regexp::zero();
  }
}

/// This calculates the derivative of a regular expression with respect to a
/// string.
std::shared_ptr<Matcher::regexp>
Matcher::derivs(std::shared_ptr<Matcher::regexp> r,
                const std::shared_ptr<List<int64_t>> &cs) {
  if (std::holds_alternative<typename List<int64_t>::Nil>(cs->v())) {
    return r;
  } else {
    const auto &_m = *std::get_if<typename List<int64_t>::Cons>(&cs->v());
    return derivs(deriv(std::move(r), _m.d_a0), _m.d_a1);
  }
}

/// To see if cs matches r, calculate the derivative of r with respect
/// to s, and see if the resulting regexp accepts the empty string.
__attribute__((pure)) bool
Matcher::deriv_parse(const std::shared_ptr<Matcher::regexp> &r,
                     const std::shared_ptr<List<int64_t>> &cs) {
  if (accepts_null(derivs(r, cs))) {
    return true;
  } else {
    return false;
  }
}

/// null r returns Eps or Zero
__attribute__((pure)) bool
Matcher::NullEpsOrZero(const std::shared_ptr<Matcher::regexp> &r) {
  if (std::holds_alternative<typename Matcher::regexp::Eps>(r->v())) {
    return true;
  } else if (std::holds_alternative<typename Matcher::regexp::Cat>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Cat>(&r->v());
    if (NullEpsOrZero(_m.d_r1)) {
      if (NullEpsOrZero(_m.d_r2)) {
        return true;
      } else {
        return false;
      }
    } else {
      if (NullEpsOrZero(_m.d_r2)) {
        return false;
      } else {
        return false;
      }
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Alt>(r->v())) {
    const auto &_m = *std::get_if<typename Matcher::regexp::Alt>(&r->v());
    if (NullEpsOrZero(_m.d_r1)) {
      if (NullEpsOrZero(_m.d_r2)) {
        return true;
      } else {
        return true;
      }
    } else {
      if (NullEpsOrZero(_m.d_r2)) {
        return true;
      } else {
        return false;
      }
    }
  } else if (std::holds_alternative<typename Matcher::regexp::Star>(r->v())) {
    return true;
  } else {
    return false;
  }
}

/// From this, we can build a decidable regexp matcher by running
/// the derivative-based parser.
__attribute__((pure)) bool
Matcher::parse(const std::shared_ptr<Matcher::regexp> &r,
               const std::shared_ptr<List<int64_t>> &cs) {
  bool b = deriv_parse(r, cs);
  if (b) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
Matcher::parse_bool(const std::shared_ptr<Matcher::regexp> &r,
                    const std::shared_ptr<List<int64_t>> &cs) {
  if (parse(r, cs)) {
    return true;
  } else {
    return false;
  }
}
