#include <levenshtein.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Levenshtein::chain>
Levenshtein::same_chain(const std::shared_ptr<String> &s) {
  if (std::holds_alternative<typename String::EmptyString>(s->v())) {
    return chain::empty();
  } else {
    const auto &_m = *std::get_if<typename String::String0>(&s->v());
    return chain::skip(_m.d_a0, _m.d_a1, _m.d_a1, Nat::o(),
                       same_chain(_m.d_a1));
  }
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  if (std::holds_alternative<typename String::EmptyString>(s1->v())) {
    return _inserts_chain_F<std::shared_ptr<Levenshtein::chain>>(s2);
  } else {
    const auto &_m = *std::get_if<typename String::String0>(&s1->v());
    return inserts_chain(_m.d_a1, s2)
        ->insert_chain(_m.d_a0, s2, _m.d_a1->append(s2), _m.d_a1->length());
  }
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain_empty(const std::shared_ptr<String> &s) {
  if (std::holds_alternative<typename String::EmptyString>(s->v())) {
    return chain::empty();
  } else {
    const auto &_m = *std::get_if<typename String::String0>(&s->v());
    return inserts_chain_empty(_m.d_a1)->insert_chain(
        _m.d_a0, String::emptystring(), _m.d_a1, _m.d_a1->length());
  }
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  if (std::holds_alternative<typename String::EmptyString>(s1->v())) {
    return same_chain(s2);
  } else {
    const auto &_m = *std::get_if<typename String::String0>(&s1->v());
    return deletes_chain(_m.d_a1, s2)
        ->delete_chain(_m.d_a0, _m.d_a1->append(s2), s2, _m.d_a1->length());
  }
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain_empty(const std::shared_ptr<String> &s) {
  if (std::holds_alternative<typename String::EmptyString>(s->v())) {
    return chain::empty();
  } else {
    const auto &_m = *std::get_if<typename String::String0>(&s->v());
    return deletes_chain_empty(_m.d_a1)->delete_chain(
        _m.d_a0, _m.d_a1, String::emptystring(), _m.d_a1->length());
  }
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::aux_both_empty(const std::shared_ptr<String> &,
                            const std::shared_ptr<String> &) {
  return chain::empty();
}

std::shared_ptr<SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>>
Levenshtein::levenshtein_chain(const std::shared_ptr<String> &s,
                               std::shared_ptr<String> _x0) {
  std::function<std::shared_ptr<
      SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>>(
      std::shared_ptr<String>)>
      levenshtein_chain1;
  levenshtein_chain1 = [&](std::shared_ptr<String> t)
      -> std::shared_ptr<
          SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>> {
    if (std::holds_alternative<typename String::EmptyString>(s->v())) {
      if (std::holds_alternative<typename String::EmptyString>(t->v())) {
        return SigT<std::shared_ptr<Nat>,
                    std::shared_ptr<Levenshtein::chain>>::existt(Nat::o(),
                                                                 aux_both_empty(
                                                                     s, t));
      } else {
        return SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>::
            existt(t->length(), inserts_chain_empty(t));
      }
    } else {
      const auto &_m = *std::get_if<typename String::String0>(&s->v());
      if (std::holds_alternative<typename String::EmptyString>(t->v())) {
        return SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>::
            existt(s->length(),
                   deletes_chain_empty(String::string0(_m.d_a0, _m.d_a1)));
      } else {
        const auto &_m0 = *std::get_if<typename String::String0>(&t->v());
        switch (_m.d_a0->ascii_dec(_m0.d_a0)) {
        case Sumbool::e_LEFT: {
          auto &&_sv1 = levenshtein_chain(_m.d_a1, _m0.d_a1);
          const auto &_m1 = *std::get_if<
              typename SigT<std::shared_ptr<Nat>,
                            std::shared_ptr<Levenshtein::chain>>::ExistT>(
              &_sv1->v());
          return SigT<std::shared_ptr<Nat>,
                      std::shared_ptr<Levenshtein::chain>>::
              existt(_m1.d_x,
                     _m1.d_a1->aux_eq_char(s, t, _m.d_a0, _m.d_a1, _m0.d_a0,
                                           _m0.d_a1, _m1.d_x));
        }
        case Sumbool::e_RIGHT: {
          auto &&_sv2 = levenshtein_chain1(_m0.d_a1);
          const auto &_m2 = *std::get_if<
              typename SigT<std::shared_ptr<Nat>,
                            std::shared_ptr<Levenshtein::chain>>::ExistT>(
              &_sv2->v());
          auto &&_sv3 =
              levenshtein_chain(_m.d_a1, String::string0(_m0.d_a0, _m0.d_a1));
          const auto &_m3 = *std::get_if<
              typename SigT<std::shared_ptr<Nat>,
                            std::shared_ptr<Levenshtein::chain>>::ExistT>(
              &_sv3->v());
          auto &&_sv4 = levenshtein_chain(_m.d_a1, _m0.d_a1);
          const auto &_m4 = *std::get_if<
              typename SigT<std::shared_ptr<Nat>,
                            std::shared_ptr<Levenshtein::chain>>::ExistT>(
              &_sv4->v());
          std::shared_ptr<Levenshtein::chain> r1_ = _m2.d_a1->aux_insert(
              s, t, _m.d_a0, _m.d_a1, _m0.d_a0, _m0.d_a1, _m2.d_x);
          std::shared_ptr<Levenshtein::chain> r2_ = _m3.d_a1->aux_delete(
              s, t, _m.d_a0, _m.d_a1, _m0.d_a0, _m0.d_a1, _m3.d_x);
          std::shared_ptr<Levenshtein::chain> r3_ = _m4.d_a1->aux_update(
              s, t, _m.d_a0, _m.d_a1, _m0.d_a0, _m0.d_a1, _m4.d_x);
          return min3_app<std::shared_ptr<
              SigT<std::shared_ptr<Nat>, std::shared_ptr<Levenshtein::chain>>>>(
              SigT<std::shared_ptr<Nat>,
                   std::shared_ptr<Levenshtein::chain>>::existt(Nat::s(_m2.d_x),
                                                                r1_),
              SigT<std::shared_ptr<Nat>,
                   std::shared_ptr<Levenshtein::chain>>::existt(Nat::s(_m3.d_x),
                                                                r2_),
              SigT<std::shared_ptr<Nat>,
                   std::shared_ptr<Levenshtein::chain>>::existt(Nat::s(_m4.d_x),
                                                                r3_),
              [](const auto &_x) { return _x->projT1(); });
        }
        default:
          std::unreachable();
        }
      }
    }
  };
  return levenshtein_chain1(_x0);
}

std::shared_ptr<Nat>
Levenshtein::levenshtein_computed(const std::shared_ptr<String> &s,
                                  const std::shared_ptr<String> &t) {
  return levenshtein_chain(s, t)->projT1();
}

std::shared_ptr<Nat>
Levenshtein::levenshtein(const std::shared_ptr<String> &_x0,
                         const std::shared_ptr<String> &_x1) {
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
