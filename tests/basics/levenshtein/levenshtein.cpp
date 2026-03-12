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
                   return chain::ctor::empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   std::shared_ptr<Ascii> a = _args._a0;
                   std::shared_ptr<String> s0 = _args._a1;
                   return chain::ctor::skip_(std::move(a), s0, s0,
                                             Nat::ctor::O_(), same_chain(s0));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::insert_chain(std::shared_ptr<Ascii> c, std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::change_(s1, String::ctor::String0_(c, s1),
                              String::ctor::String0_(c, s2), n,
                              edit::ctor::insertion_(c, s1),
                              chain::ctor::skip_(c, s1, s2, n, std::move(c0)));
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
                   std::shared_ptr<Ascii> a = _args._a0;
                   std::shared_ptr<String> s = _args._a1;
                   return insert_chain(std::move(a), s2, s->append(s2),
                                       s->length(), inserts_chain(s, s2));
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::inserts_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString _args) -> auto {
                   return chain::ctor::empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   std::shared_ptr<Ascii> a = _args._a0;
                   std::shared_ptr<String> s0 = _args._a1;
                   return insert_chain(std::move(a),
                                       String::ctor::EmptyString_(), s0,
                                       s0->length(), inserts_chain_empty(s0));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::delete_chain(std::shared_ptr<Ascii> c, std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::change_(String::ctor::String0_(c, s1), s1, std::move(s2),
                              std::move(n), edit::ctor::deletion_(c, s1),
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
                   std::shared_ptr<Ascii> a = _args._a0;
                   std::shared_ptr<String> s = _args._a1;
                   return delete_chain(std::move(a), s->append(s2), s2,
                                       s->length(), deletes_chain(s, s2));
                 }},
      s1->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::deletes_chain_empty(const std::shared_ptr<String> &s) {
  return std::visit(
      Overloaded{[](const typename String::EmptyString _args) -> auto {
                   return chain::ctor::empty_();
                 },
                 [](const typename String::String0 _args) -> auto {
                   std::shared_ptr<Ascii> a = _args._a0;
                   std::shared_ptr<String> s0 = _args._a1;
                   return delete_chain(std::move(a), s0,
                                       String::ctor::EmptyString_(),
                                       s0->length(), deletes_chain_empty(s0));
                 }},
      s->v());
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::update_chain(std::shared_ptr<Ascii> c, std::shared_ptr<Ascii> c_,
                          std::shared_ptr<String> s1,
                          std::shared_ptr<String> s2, std::shared_ptr<Nat> n,
                          std::shared_ptr<Levenshtein::chain> c0) {
  return chain::ctor::change_(
      String::ctor::String0_(c, s1), String::ctor::String0_(c_, s1),
      String::ctor::String0_(c_, s2), n, edit::ctor::update_(c, c_, s1),
      chain::ctor::skip_(c_, s1, s2, n, std::move(c0)));
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
  return chain::ctor::skip_(std::move(y), std::move(xs), std::move(ys),
                            std::move(n), std::move(c));
}

std::shared_ptr<Levenshtein::chain>
Levenshtein::aux_both_empty(const std::shared_ptr<String> &_x,
                            const std::shared_ptr<String> &_x0) {
  return chain::ctor::empty_();
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
                      [&](const typename String::EmptyString _args)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            existT_(Nat::ctor::O_(),
                                    aux_both_empty(s, std::move(t)));
                      },
                      [&](const typename String::String0 _args)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            existT_(t->length(), inserts_chain_empty(t));
                      }},
                  t->v());
            },
            [&](const typename String::String0 _args)
                -> std::shared_ptr<SigT<std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>> {
              std::shared_ptr<Ascii> x = _args._a0;
              std::shared_ptr<String> xs = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString _args)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        return SigT<std::shared_ptr<Nat>,
                                    std::shared_ptr<Levenshtein::chain>>::ctor::
                            existT_(s->length(),
                                    deletes_chain_empty(String::ctor::String0_(
                                        std::move(x), std::move(xs))));
                      },
                      [&](const typename String::String0 _args)
                          -> std::shared_ptr<
                              SigT<std::shared_ptr<Nat>,
                                   std::shared_ptr<Levenshtein::chain>>> {
                        std::shared_ptr<Ascii> y = _args._a0;
                        std::shared_ptr<String> ys = _args._a1;
                        return [&](void) {
                          switch (x->ascii_dec(y)) {
                          case sumbool::left: {
                            return std::visit(
                                Overloaded{
                                    [&](const typename SigT<
                                        std::shared_ptr<Nat>,
                                        std::shared_ptr<Levenshtein::chain>>::
                                            existT _args)
                                        -> std::shared_ptr<
                                            SigT<std::shared_ptr<Nat>,
                                                 std::shared_ptr<
                                                     Levenshtein::chain>>> {
                                      std::shared_ptr<Nat> n = _args._a0;
                                      std::shared_ptr<Levenshtein::chain> c =
                                          _args._a1;
                                      return SigT<
                                          std::shared_ptr<Nat>,
                                          std::shared_ptr<Levenshtein::chain>>::
                                          ctor::existT_(
                                              n, aux_eq_char(s, std::move(t),
                                                             std::move(x),
                                                             std::move(xs),
                                                             std::move(y),
                                                             std::move(ys), n,
                                                             std::move(c)));
                                    }},
                                levenshtein_chain(xs, ys)->v());
                          }
                          case sumbool::right: {
                            return std::visit(
                                Overloaded{[&](const typename SigT<
                                               std::shared_ptr<Nat>,
                                               std::shared_ptr<
                                                   Levenshtein::chain>>::existT
                                                   _args)
                                               -> std::shared_ptr<SigT<
                                                   std::shared_ptr<Nat>,
                                                   std::shared_ptr<
                                                       Levenshtein::chain>>> {
                                  std::shared_ptr<Nat> n1 = _args._a0;
                                  std::shared_ptr<Levenshtein::chain> r1 =
                                      _args._a1;
                                  return std::visit(
                                      Overloaded{[&](const typename SigT<
                                                     std::shared_ptr<Nat>,
                                                     std::shared_ptr<
                                                         Levenshtein::chain>>::
                                                         existT _args)
                                                     -> std::shared_ptr<SigT<
                                                         std::shared_ptr<Nat>,
                                                         std::shared_ptr<
                                                             Levenshtein::
                                                                 chain>>> {
                                        std::shared_ptr<Nat> n2 = _args._a0;
                                        std::shared_ptr<Levenshtein::chain> r2 =
                                            _args._a1;
                                        return std::visit(
                                            Overloaded{
                                                [&](const typename SigT<
                                                    std::shared_ptr<Nat>,
                                                    std::shared_ptr<
                                                        Levenshtein::chain>>::
                                                        existT _args)
                                                    -> std::shared_ptr<SigT<
                                                        std::shared_ptr<Nat>,
                                                        std::shared_ptr<
                                                            Levenshtein::
                                                                chain>>> {
                                                  std::shared_ptr<Nat> n3 =
                                                      _args._a0;
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r3 = _args._a1;
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r1_ = aux_insert(
                                                          s, std::move(t),
                                                          std::move(x),
                                                          std::move(xs),
                                                          std::move(y),
                                                          std::move(ys),
                                                          std::move(n1),
                                                          std::move(r1));
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r2_ = aux_delete(
                                                          s, std::move(t),
                                                          std::move(x),
                                                          std::move(xs),
                                                          std::move(y),
                                                          std::move(ys),
                                                          std::move(n2),
                                                          std::move(r2));
                                                  std::shared_ptr<
                                                      Levenshtein::chain>
                                                      r3_ = aux_update(
                                                          s, std::move(t),
                                                          std::move(x),
                                                          std::move(xs),
                                                          std::move(y),
                                                          std::move(ys),
                                                          std::move(n3),
                                                          std::move(r3));
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
                                                          ctor::existT_(
                                                              Nat::ctor::S_(
                                                                  std::move(
                                                                      n1)),
                                                              std::move(r1_)),
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>::
                                                          ctor::existT_(
                                                              Nat::ctor::S_(
                                                                  std::move(
                                                                      n2)),
                                                              std::move(r2_)),
                                                      SigT<std::shared_ptr<Nat>,
                                                           std::shared_ptr<
                                                               Levenshtein::
                                                                   chain>>::
                                                          ctor::existT_(
                                                              Nat::ctor::S_(
                                                                  std::move(
                                                                      n3)),
                                                              std::move(r3_)),
                                                      [](const auto &_x) {
                                                        return _x->projT1();
                                                      });
                                                }},
                                            levenshtein_chain(xs, ys)->v());
                                      }},
                                      levenshtein_chain(
                                          xs, String::ctor::String0_(y, ys))
                                          ->v());
                                }},
                                levenshtein_chain1(ys)->v());
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

sumbool Bool::bool_dec(const bool0 b1, const bool0 b2) {
  return [&](void) {
    switch (b1) {
    case bool0::true0: {
      return [&](void) {
        switch (b2) {
        case bool0::true0: {
          return sumbool::left;
        }
        case bool0::false0: {
          return sumbool::right;
        }
        }
      }();
    }
    case bool0::false0: {
      return [&](void) {
        switch (b2) {
        case bool0::true0: {
          return sumbool::right;
        }
        case bool0::false0: {
          return sumbool::left;
        }
        }
      }();
    }
    }
  }();
}
