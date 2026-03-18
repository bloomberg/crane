#include <levenshtein.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Levenshtein::chain>
Levenshtein::same_chain(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString _args) -> auto {
                   return chain::ctor::Empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   return chain::ctor::Skip_(_args.d_a0, _args.d_a1, _args.d_a1,
                                             Nat::ctor::O_(),
                                             same_chain(_args.d_a1));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::insert_chain(std::shared_ptr<Ascii> c, std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::Change_(s1, String::ctor::String0_(c, s1),
                              String::ctor::String0_(c, s2), n,
                              edit::ctor::Insertion_(c, s1),
                              chain::ctor::Skip_(c, s1, s2, n, std::move(c0)));
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString _args) -> auto {
                   return _inserts_chain_F<std::shared_ptr<Levenshtein::chain>>(
                       s2);
                 },
                 [&](const typename String::String0 _args) -> auto {
                   return insert_chain(_args.d_a0, s2, _args.d_a1->append(s2),
                                       _args.d_a1->length(),
                                       inserts_chain(_args.d_a1, s2));
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString _args) -> auto {
                   return chain::ctor::Empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   return insert_chain(_args.d_a0, String::ctor::EmptyString_(),
                                       _args.d_a1, _args.d_a1->length(),
                                       inserts_chain_empty(_args.d_a1));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::delete_chain(std::shared_ptr<Ascii> c, std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::Change_(String::ctor::String0_(c, s1), s1, std::move(s2),
                              std::move(n), edit::ctor::Deletion_(c, s1),
                              std::move(c0));
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain(const std::shared_ptr<String> &s1,
                           const std::shared_ptr<String> &s2) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString _args) -> auto {
                   return same_chain(s2);
                 },
                 [&](const typename String::String0 _args) -> auto {
                   return delete_chain(_args.d_a0, _args.d_a1->append(s2), s2,
                                       _args.d_a1->length(),
                                       deletes_chain(_args.d_a1, s2));
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString _args) -> auto {
                   return chain::ctor::Empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   return delete_chain(
                       _args.d_a0, _args.d_a1, String::ctor::EmptyString_(),
                       _args.d_a1->length(), deletes_chain_empty(_args.d_a1));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::update_chain(std::shared_ptr<Ascii> c, std::shared_ptr<Ascii> c_,
                          std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::Change_(
      String::ctor::String0_(c, s1), String::ctor::String0_(c_, s1),
      String::ctor::String0_(c_, s2), n, edit::ctor::Update_(c, c_, s1),
      chain::ctor::Skip_(c_, s1, s2, n, std::move(c0)));
}

std::shared_ptr<Levenshtein::chain> Levenshtein::aux_insert(
    const std::shared_ptr<String> &_x, const std::shared_ptr<String> &_x0,
    std::shared_ptr<Ascii> x, std::shared_ptr<String> xs,
    const std::shared_ptr<Ascii> &y, const std::shared_ptr<String> &ys,
    const std::shared_ptr<Nat> &n,
    const std::shared_ptr<Levenshtein::chain> &r1) {
  return insert_chain(y, String::ctor::String0_(std::move(x), std::move(xs)),
                      ys, n, r1);
}

std::shared_ptr<Levenshtein::chain> Levenshtein::aux_delete(
    const std::shared_ptr<String> &_x, const std::shared_ptr<String> &_x0,
    const std::shared_ptr<Ascii> &x, const std::shared_ptr<String> &xs,
    std::shared_ptr<Ascii> y, std::shared_ptr<String> ys,
    const std::shared_ptr<Nat> &n,
    const std::shared_ptr<Levenshtein::chain> &r2) {
  return delete_chain(
      x, xs, String::ctor::String0_(std::move(y), std::move(ys)), n, r2);
}

std::shared_ptr<Levenshtein::chain> Levenshtein::aux_update(
    const std::shared_ptr<String> &_x, const std::shared_ptr<String> &_x0,
    const std::shared_ptr<Ascii> &x, const std::shared_ptr<String> &xs,
    const std::shared_ptr<Ascii> &y, const std::shared_ptr<String> &ys,
    const std::shared_ptr<Nat> &n,
    const std::shared_ptr<Levenshtein::chain> &r3) {
  return update_chain(x, y, xs, ys, n, r3);
}

std::shared_ptr<Levenshtein::chain> Levenshtein::aux_eq_char(
    const std::shared_ptr<String> &_x, const std::shared_ptr<String> &_x0,
    const std::shared_ptr<Ascii> &_x1, std::shared_ptr<String> xs,
    std::shared_ptr<Ascii> y, std::shared_ptr<String> ys,
    std::shared_ptr<Nat> n, std::shared_ptr<Levenshtein::chain> c) {
  return chain::ctor::Skip_(std::move(y), std::move(xs), std::move(ys),
                            std::move(n), std::move(c));
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::aux_both_empty(const std::shared_ptr<String> &_x,
                            const std::shared_ptr<String> &_x0) {
  return chain::ctor::Empty_();
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
            [&](const typename String::EmptyString _args)
                -> std::shared_ptr<SigT<std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString _args0)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            ExistT_(Nat::ctor::O_(),
                                    aux_both_empty(s, std::move(t)));
                      },
                      [&](const typename String::String0 _args0)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            ExistT_(t->length(), inserts_chain_empty(t));
                      }},
                  t->v());
            },
            [&](const typename String::String0 _args)
                -> std::shared_ptr<SigT<std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString _args0)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            ExistT_(s->length(),
                                    deletes_chain_empty(String::ctor::String0_(
                                        _args.d_a0, _args.d_a1)));
                      },
                      [&](const typename String::String0 _args0)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return [&](void) {
                          switch (_args.d_a0->ascii_dec(_args0.d_a0)) {
                          case Sumbool::e_LEFT: {
                            return std::visit(
                                Overloaded{
                                    [&](const typename SigT<
                                        std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>::
                                            ExistT _args1)
                                        -> std::shared_ptr<
                                            SigT<std::shared_ptr<Nat>,
                                                 std::shared_ptr<
                                                     Levenshtein::chain>>> {
                                      return SigT<
                                          std::shared_ptr<Nat>,
                                          std::shared_ptr<Levenshtein::chain>>::
                                          ctor::ExistT_(
                                              _args1.d_a0,
                                              aux_eq_char(
                                                  s, std::move(t), _args.d_a0,
                                                  _args.d_a1, _args0.d_a0,
                                                  _args0.d_a1, _args1.d_a0,
                                                  _args1.d_a1));
                                    }},
                                levenshtein_chain(_args.d_a1, _args0.d_a1)
                                    ->v());
                          }
                          case Sumbool::e_RIGHT: {
                            return std::visit(
                                Overloaded{[&](const typename SigT<
                                               std::shared_ptr<Nat>,
                                               std::shared_ptr<
                                                   Levenshtein::chain>>::ExistT
                                                   _args2)
                                               -> std::shared_ptr<SigT<
                                                   std::shared_ptr<Nat>,
                                                   std::shared_ptr<
                                                       Levenshtein::chain>>> {
                                  return std::visit(
                                      Overloaded{[&](const typename SigT<
                                                     std::shared_ptr<Nat>,
                                                     std::shared_ptr<
                                                         Levenshtein::chain>>::
                                                         ExistT _args3)
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
                                                        ExistT _args4)
                                                    -> std::shared_ptr<SigT<
                                                        std::shared_ptr<Nat>,
                                                        std::shared_ptr<
                                                            Levenshtein::
                                                                chain>>> {
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r1_ = aux_insert(
                                                          s, t, _args.d_a0,
                                                          _args.d_a1,
                                                          _args0.d_a0,
                                                          _args0.d_a1,
                                                          _args2.d_a0,
                                                          _args2.d_a1);
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r2_ = aux_delete(
                                                          s, t, _args.d_a0,
                                                          _args.d_a1,
                                                          _args0.d_a0,
                                                          _args0.d_a1,
                                                          _args3.d_a0,
                                                          _args3.d_a1);
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r3_ = aux_update(
                                                          s, std::move(t),
                                                          _args.d_a0,
                                                          _args.d_a1,
                                                          _args0.d_a0,
                                                          _args0.d_a1,
                                                          _args4.d_a0,
                                                          _args4.d_a1);
                                                  return min3_app<
                                                      std::shared_ptr<SigT<
                                                          std::shared_ptr<Nat>,
                                                          std::shared_ptr<
                                                              Levenshtein::
                                                                  chain>>>>(
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>::
                                                          ctor::ExistT_(
                                                              Nat::ctor::S_(
                                                                  _args2.d_a0),
                                                              std::move(r1_)),
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>::
                                                          ctor::ExistT_(
                                                              Nat::ctor::S_(
                                                                  _args3.d_a0),
                                                              std::move(r2_)),
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>::
                                                          ctor::ExistT_(
                                                              Nat::ctor::S_(
                                                                  _args4.d_a0),
                                                              std::move(r3_)),
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
                                          String::ctor::String0_(_args0.d_a0,
                                                                 _args0.d_a1))
                                          ->v());
                                }},
                                levenshtein_chain1(_args0.d_a1)->v());
                          }
                          }
                        }();
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
  return [&](void) {
    switch (b1) {
    case Bool0::e_TRUE0: {
      return [&](void) {
        switch (b2) {
        case Bool0::e_TRUE0: {
          return Sumbool::e_LEFT;
        }
        case Bool0::e_FALSE0: {
          return Sumbool::e_RIGHT;
        }
        }
      }();
    }
    case Bool0::e_FALSE0: {
      return [&](void) {
        switch (b2) {
        case Bool0::e_TRUE0: {
          return Sumbool::e_RIGHT;
        }
        case Bool0::e_FALSE0: {
          return Sumbool::e_LEFT;
        }
        }
      }();
    }
    }
  }();
}
