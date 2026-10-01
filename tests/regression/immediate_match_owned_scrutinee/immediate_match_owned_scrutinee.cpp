#include "immediate_match_owned_scrutinee.h"

/// A match in argument position becomes an immediately invoked lambda,
/// std::make_optional<Nat>([...]() { ... n.v_mut() ... }()).  The
/// scrutinee n is an owned local, so the match destructures it through
/// v_mut().  return_captures_by_value made that lambda a Closure
/// because it sits in a returned expression, and a closure's captures are
/// const since a0357147d, so v_mut() on the captured Nat did not
/// compile.  A lambda invoked where it is written is never stored: it stays
/// Immediate and captures by reference.  Found in Vellvm's
/// FMapFacts.cardinal_inv_2b.
Nat ImmediateMatchOwnedScrutinee::count(const List<Nat> &l) {
  if (std::holds_alternative<typename List<Nat>::Nil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] = std::get<typename List<Nat>::Cons>(l.v());
    return Nat::s(count(*a1));
  }
}

std::optional<Nat> ImmediateMatchOwnedScrutinee::pred_count(List<Nat> l) {
  Nat n = count(l);
  crane::fn<Nat(Nat)> g = [=](const Nat &k) {
    return count(List<Nat>::cons(k, l));
  };
  return std::make_optional<Nat>([&]() {
    if (std::holds_alternative<typename Nat::O>(n.v_mut())) {
      return Nat::o();
    } else {
      auto &[a0] = std::get<typename Nat::S>(n.v_mut());
      return g(*a0);
    }
  }());
}

bool ImmediateMatchOwnedScrutinee::check(std::monostate) {
  auto _cs = pred_count(List<Nat>::cons(
      Nat::s(Nat::o()),
      List<Nat>::cons(Nat::s(Nat::s(Nat::o())),
                      List<Nat>::cons(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                      List<Nat>::nil()))));
  if (_cs.has_value()) {
    const Nat &n = *_cs;
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return false;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(n.v());
      auto &&_sv0 = *a0;
      if (std::holds_alternative<typename Nat::O>(_sv0.v())) {
        return false;
      } else {
        const auto &[a00] = std::get<typename Nat::S>(_sv0.v());
        auto &&_sv1 = *a00;
        if (std::holds_alternative<typename Nat::O>(_sv1.v())) {
          return false;
        } else {
          const auto &[a01] = std::get<typename Nat::S>(_sv1.v());
          auto &&_sv2 = *a01;
          if (std::holds_alternative<typename Nat::O>(_sv2.v())) {
            return false;
          } else {
            const auto &[a02] = std::get<typename Nat::S>(_sv2.v());
            auto &&_sv = *a02;
            if (std::holds_alternative<typename Nat::O>(_sv.v())) {
              return true;
            } else {
              return false;
            }
          }
        }
      }
    }
  } else {
    return false;
  }
}
