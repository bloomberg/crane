#include <levenshtein.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Levenshtein::chain>
Levenshtein::same_chain(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString &) -> auto {
                   return chain::empty();
                 },
                 [](const typename String::String0 &_args) -> auto {
                   return chain::skip(_args.d_a0, _args.d_a1, _args.d_a1,
                                      Nat::o(), same_chain(_args.d_a1));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString &) -> auto {
                   return _inserts_chain_F<std::shared_ptr<Levenshtein::chain>>(
                       s2);
                 },
                 [&](const typename String::String0 &_args) -> auto {
                   return inserts_chain(_args.d_a1, s2)
                       ->insert_chain(_args.d_a0, s2, _args.d_a1->append(s2),
                                      _args.d_a1->length());
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString &) -> auto {
                   return chain::empty();
                 },
                 [](const typename String::String0 &_args) -> auto {
                   return inserts_chain_empty(_args.d_a1)
                       ->insert_chain(_args.d_a0, String::emptystring(),
                                      _args.d_a1, _args.d_a1->length());
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString &) -> auto {
                   return same_chain(s2);
                 },
                 [&](const typename String::String0 &_args) -> auto {
                   return deletes_chain(_args.d_a1, s2)
                       ->delete_chain(_args.d_a0, _args.d_a1->append(s2), s2,
                                      _args.d_a1->length());
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString &) -> auto {
                   return chain::empty();
                 },
                 [](const typename String::String0 &_args) -> auto {
                   return deletes_chain_empty(_args.d_a1)
                       ->delete_chain(_args.d_a0, _args.d_a1,
                                      String::emptystring(),
                                      _args.d_a1->length());
                 }},
      s->v());
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
    return std::visit(
        Overloaded{
            [&](const typename String::EmptyString &)
                -> std::shared_ptr<SigT<std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString &)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::
                            existt(Nat::o(), aux_both_empty(s, t));
                      },
                      [&](const typename String::String0 &)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::
                            existt(t->length(), inserts_chain_empty(t));
                      }},
                  t->v());
            },
            [&](const typename String::String0 &_args)
                -> std::shared_ptr<SigT<std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString &)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::
                            existt(s->length(),
                                   deletes_chain_empty(String::string0(
                                       _args.d_a0, _args.d_a1)));
                      },
                      [&](const typename String::String0 &_args0)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        switch (_args.d_a0->ascii_dec(_args0.d_a0)) {
                        case Sumbool::e_LEFT: {
                          return std::visit(
                              Overloaded{
                                  [&](const typename SigT<
                                      std::shared_ptr<Nat>,
                                      std::shared_ptr<Levenshtein::chain>>::
                                          ExistT &_args1)
                                      -> std::shared_ptr<
                                          SigT<std::shared_ptr<Nat>,
                                               std::shared_ptr<
                                                   Levenshtein::chain>>> {
                                    return SigT<
                                        std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>::
                                        existt(_args1.d_x,
                                               _args1.d_a1->aux_eq_char(
                                                   s, t, _args.d_a0, _args.d_a1,
                                                   _args0.d_a0, _args0.d_a1,
                                                   _args1.d_x));
                                  }},
                              levenshtein_chain(_args.d_a1, _args0.d_a1)->v());
                        }
                        case Sumbool::e_RIGHT: {
                          return std::visit(
                              Overloaded{[&](const typename SigT<
                                             std::shared_ptr<Nat>,
                                             std::shared_ptr<
                                                 Levenshtein::chain>>::ExistT
                                                 &_args2)
                                             -> std::shared_ptr<SigT<
                                                 std::shared_ptr<Nat>,
                                                 std::shared_ptr<
                                                     Levenshtein::chain>>> {
                                return std::visit(
                                    Overloaded{[&](const typename SigT<
                                                   std::shared_ptr<Nat>,
                                                   std::shared_ptr<
                                                       Levenshtein::chain>>::
                                                       ExistT &_args3)
                                                   -> std::shared_ptr<SigT<
                                                       std::shared_ptr<Nat>,
                                                       std::shared_ptr<
                                                           Levenshtein::
                                                               chain>>> {
                                      return std::visit(
                                          Overloaded{
                                              [&](const typename SigT<
                                                  std::shared_ptr<Nat>,
                                                  std::shared_ptr<
                                                      Levenshtein::chain>>::
                                                      ExistT &_args4)
                                                  -> std::shared_ptr<
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>> {
                                                std::shared_ptr<
                                                    Levenshtein::chain>
                                                    r1_ =
                                                        _args2.d_a1->aux_insert(
                                                            s, t, _args.d_a0,
                                                            _args.d_a1,
                                                            _args0.d_a0,
                                                            _args0.d_a1,
                                                            _args2.d_x);
                                                std::shared_ptr<
                                                    Levenshtein::chain>
                                                    r2_ =
                                                        _args3.d_a1->aux_delete(
                                                            s, t, _args.d_a0,
                                                            _args.d_a1,
                                                            _args0.d_a0,
                                                            _args0.d_a1,
                                                            _args3.d_x);
                                                std::shared_ptr<
                                                    Levenshtein::chain>
                                                    r3_ =
                                                        _args4.d_a1->aux_update(
                                                            s, t, _args.d_a0,
                                                            _args.d_a1,
                                                            _args0.d_a0,
                                                            _args0.d_a1,
                                                            _args4.d_x);
                                                return min3_app<std::shared_ptr<
                                                    SigT<std::shared_ptr<Nat>,
                                                         std::shared_ptr<
                                                             Levenshtein::
                                                                 chain>>>>(
                                                    SigT<std::shared_ptr<Nat>,
                                                         std::shared_ptr<
                                                             Levenshtein::
                                                                 chain>>::
                                                        existt(
                                                            Nat::s(_args2.d_x),
                                                            r1_),
                                                    SigT<std::shared_ptr<Nat>,
                                                         std::shared_ptr<
                                                             Levenshtein::
                                                                 chain>>::
                                                        existt(
                                                            Nat::s(_args3.d_x),
                                                            r2_),
                                                    SigT<std::shared_ptr<Nat>,
                                                         std::shared_ptr<
                                                             Levenshtein::
                                                                 chain>>::
                                                        existt(
                                                            Nat::s(_args4.d_x),
                                                            r3_),
                                                    [](const auto &_x) {
                                                      return _x->projT1();
                                                    });
                                              }},
                                          levenshtein_chain(_args.d_a1,
                                                            _args0.d_a1)
                                              ->v());
                                    }},
                                    levenshtein_chain(
                                        _args.d_a1,
                                        String::string0(_args0.d_a0,
                                                        _args0.d_a1))
                                        ->v());
                              }},
                              levenshtein_chain1(_args0.d_a1)->v());
                        }
                        default:
                          std::unreachable();
                        }
                      }},
                  t->v());
            }},
        s->v());
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
