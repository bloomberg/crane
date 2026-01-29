#include <any>
#include <functional>
#include <iostream>
#include <levenshtein.h>
#include <memory>
#include <string>
#include <variant>

std::shared_ptr<Bool0::bool0> leb(const std::shared_ptr<Nat::nat> &n,
                                  const std::shared_ptr<Nat::nat> &m) {
  return std::visit(
      Overloaded{[](const typename Nat::nat::O _args)
                     -> std::shared_ptr<Bool0::bool0> {
                   return Bool0::bool0::ctor::true0_();
                 },
                 [&](const typename Nat::nat::S _args)
                     -> std::shared_ptr<Bool0::bool0> {
                   std::shared_ptr<Nat::nat> n_ = _args._a0;
                   return std::visit(
                       Overloaded{[](const typename Nat::nat::O _args)
                                      -> std::shared_ptr<Bool0::bool0> {
                                    return Bool0::bool0::ctor::false0_();
                                  },
                                  [&](const typename Nat::nat::S _args)
                                      -> std::shared_ptr<Bool0::bool0> {
                                    std::shared_ptr<Nat::nat> m_ = _args._a0;
                                    return leb(n_, m_);
                                  }},
                       m->v());
                 }},
      n->v());
}

std::shared_ptr<Sumbool::sumbool>
bool_dec(const std::shared_ptr<Bool0::bool0> &b1,
         const std::shared_ptr<Bool0::bool0> &b2) {
  return std::visit(
      Overloaded{[&](const typename Bool0::bool0::true0 _args) -> T1 {
                   return std::visit(
                       Overloaded{[](const typename Bool0::bool0::true0 _args)
                                      -> std::shared_ptr<Sumbool::sumbool> {
                                    return Sumbool::sumbool::ctor::left_();
                                  },
                                  [](const typename Bool0::bool0::false0 _args)
                                      -> std::shared_ptr<Sumbool::sumbool> {
                                    return Sumbool::sumbool::ctor::right_();
                                  }},
                       b2->v());
                 },
                 [&](const typename Bool0::bool0::false0 _args) -> T1 {
                   return std::visit(
                       Overloaded{[](const typename Bool0::bool0::true0 _args)
                                      -> std::shared_ptr<Sumbool::sumbool> {
                                    return Sumbool::sumbool::ctor::right_();
                                  },
                                  [](const typename Bool0::bool0::false0 _args)
                                      -> std::shared_ptr<Sumbool::sumbool> {
                                    return Sumbool::sumbool::ctor::left_();
                                  }},
                       b2->v());
                 }},
      b1->v());
}

std::shared_ptr<Sumbool::sumbool>
ascii_dec(const std::shared_ptr<Ascii::ascii> &a,
          const std::shared_ptr<Ascii::ascii> &b) {
  return std::
      visit(Overloaded{[&](const typename Ascii::ascii::Ascii _args) -> T1 {
              std::shared_ptr<Bool0::bool0> b0 = _args._a0;
              std::shared_ptr<Bool0::bool0> b1 = _args._a1;
              std::shared_ptr<Bool0::bool0> b2 = _args._a2;
              std::shared_ptr<Bool0::bool0> b3 = _args._a3;
              std::shared_ptr<Bool0::bool0> b4 = _args._a4;
              std::shared_ptr<Bool0::bool0> b5 = _args._a5;
              std::shared_ptr<Bool0::bool0> b6 = _args._a6;
              std::shared_ptr<Bool0::bool0> b7 = _args._a7;
              return std::visit(Overloaded{[&](const typename Ascii::ascii::Ascii _args) -> std::
                                                                                             shared_ptr<
                                                                                                 Sumbool::
                                                                                                     sumbool> {
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b8 =
                                                                                                       _args
                                                                                                           ._a0;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b9 =
                                                                                                       _args
                                                                                                           ._a1;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b10 =
                                                                                                       _args
                                                                                                           ._a2;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b11 =
                                                                                                       _args
                                                                                                           ._a3;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b12 =
                                                                                                       _args
                                                                                                           ._a4;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b13 =
                                                                                                       _args
                                                                                                           ._a5;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b14 =
                                                                                                       _args
                                                                                                           ._a6;
                                                                                               std::shared_ptr<
                                                                                                   Bool0::
                                                                                                       bool0>
                                                                                                   b15 =
                                                                                                       _args
                                                                                                           ._a7;
                                                                                               return std::visit(
                                                                                                   Overloaded{
                                                                                                       [&](const typename Sumbool::
                                                                                                               sumbool::left
                                                                                                                   _args)
                                                                                                           -> T1 {
                                                                                                         return std::visit(
                                                                                                             Overloaded{
                                                                                                                 [&](const typename Sumbool::
                                                                                                                         sumbool::left
                                                                                                                             _args)
                                                                                                                     -> T1 {
                                                                                                                   return std::
                                                                                                                       visit(
                                                                                                                           Overloaded{[&](const typename Sumbool::
                                                                                                                                              sumbool::left
                                                                                                                                                  _args)
                                                                                                                                          -> T1 {
                                                                                                                                        return std::
                                                                                                                                            visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                                                     sumbool::left
                                                                                                                                                                         _args)
                                                                                                                                                                 -> T1 {
                                                                                                                                                               return std::visit(
                                                                                                                                                                   Overloaded{
                                                                                                                                                                       [&](const typename Sumbool::
                                                                                                                                                                               sumbool::left
                                                                                                                                                                                   _args) -> T1 {
                                                                                                                                                                         return std::visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                                                                                              sumbool::left
                                                                                                                                                                                                                  _args)
                                                                                                                                                                                                          -> T1 {
                                                                                                                                                                                                        return std::visit(
                                                                                                                                                                                                            Overloaded{
                                                                                                                                                                                                                [&](const typename Sumbool::
                                                                                                                                                                                                                        sumbool::left
                                                                                                                                                                                                                            _args)
                                                                                                                                                                                                                    -> T1 {
                                                                                                                                                                                                                  return std::visit(
                                                                                                                                                                                                                      Overloaded{
                                                                                                                                                                                                                          [](const typename Sumbool::
                                                                                                                                                                                                                                 sumbool::left
                                                                                                                                                                                                                                     _args)
                                                                                                                                                                                                                              -> T1 {
                                                                                                                                                                                                                            return Sumbool::
                                                                                                                                                                                                                                sumbool::ctor::
                                                                                                                                                                                                                                    left_();
                                                                                                                                                                                                                          },
                                                                                                                                                                                                                          [](const typename Sumbool::
                                                                                                                                                                                                                                 sumbool::right
                                                                                                                                                                                                                                     _args)
                                                                                                                                                                                                                              -> T1 {
                                                                                                                                                                                                                            return Sumbool::
                                                                                                                                                                                                                                sumbool::ctor::
                                                                                                                                                                                                                                    right_();
                                                                                                                                                                                                                          }},
                                                                                                                                                                                                                      bool_dec(
                                                                                                                                                                                                                          b7,
                                                                                                                                                                                                                          b15)
                                                                                                                                                                                                                          ->v());
                                                                                                                                                                                                                },
                                                                                                                                                                                                                [](const typename Sumbool::
                                                                                                                                                                                                                       sumbool::right
                                                                                                                                                                                                                           _args)
                                                                                                                                                                                                                    -> T1 {
                                                                                                                                                                                                                  return Sumbool::
                                                                                                                                                                                                                      sumbool::ctor::
                                                                                                                                                                                                                          right_();
                                                                                                                                                                                                                }},
                                                                                                                                                                                                            bool_dec(
                                                                                                                                                                                                                b6,
                                                                                                                                                                                                                b14)
                                                                                                                                                                                                                ->v());
                                                                                                                                                                                                      },
                                                                                                                                                                                                      [](const typename Sumbool::
                                                                                                                                                                                                             sumbool::right
                                                                                                                                                                                                                 _args)
                                                                                                                                                                                                          -> T1 {
                                                                                                                                                                                                        return Sumbool::
                                                                                                                                                                                                            sumbool::ctor::
                                                                                                                                                                                                                right_();
                                                                                                                                                                                                      }},
                                                                                                                                                                                           bool_dec(
                                                                                                                                                                                               b5,
                                                                                                                                                                                               b13)
                                                                                                                                                                                               ->v());
                                                                                                                                                                       },
                                                                                                                                                                       [](const typename Sumbool::
                                                                                                                                                                              sumbool::right
                                                                                                                                                                                  _args)
                                                                                                                                                                           -> T1 {
                                                                                                                                                                         return Sumbool::
                                                                                                                                                                             sumbool::ctor::
                                                                                                                                                                                 right_();
                                                                                                                                                                       }},
                                                                                                                                                                   bool_dec(
                                                                                                                                                                       b4,
                                                                                                                                                                       b12)
                                                                                                                                                                       ->v());
                                                                                                                                                             },
                                                                                                                                                             [](const typename Sumbool::sumbool::right _args) -> T1 {
                                                                                                                                                               return Sumbool::
                                                                                                                                                                   sumbool::ctor::
                                                                                                                                                                       right_();
                                                                                                                                                             }},
                                                                                                                                                  bool_dec(
                                                                                                                                                      b3,
                                                                                                                                                      b11)
                                                                                                                                                      ->v());
                                                                                                                                      },
                                                                                                                                      [](const typename Sumbool::
                                                                                                                                             sumbool::right
                                                                                                                                                 _args)
                                                                                                                                          -> T1 {
                                                                                                                                        return Sumbool::
                                                                                                                                            sumbool::ctor::
                                                                                                                                                right_();
                                                                                                                                      }},
                                                                                                                           bool_dec(
                                                                                                                               b2,
                                                                                                                               b10)
                                                                                                                               ->v());
                                                                                                                 },
                                                                                                                 [](const typename Sumbool::
                                                                                                                        sumbool::right
                                                                                                                            _args)
                                                                                                                     -> T1 {
                                                                                                                   return Sumbool::
                                                                                                                       sumbool::ctor::
                                                                                                                           right_();
                                                                                                                 }},
                                                                                                             bool_dec(
                                                                                                                 b1,
                                                                                                                 b9)
                                                                                                                 ->v());
                                                                                                       },
                                                                                                       [](const typename Sumbool::
                                                                                                              sumbool::right
                                                                                                                  _args)
                                                                                                           -> T1 {
                                                                                                         return Sumbool::
                                                                                                             sumbool::ctor::
                                                                                                                 right_();
                                                                                                       }},
                                                                                                   bool_dec(
                                                                                                       b0,
                                                                                                       b8)
                                                                                                       ->v());
                                                                                             }},
                                b->v());
            }},
            a->v());
}

std::shared_ptr<Nat::nat> length(const std::shared_ptr<String::string> &s) {
  return std::visit(
      Overloaded{
          [](const typename String::string::EmptyString _args)
              -> std::shared_ptr<Nat::nat> { return Nat::nat::ctor::O_(); },
          [](const typename String::string::String _args)
              -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<String::string> s_ = _args._a1;
            return Nat::nat::ctor::S_(length(s_));
          }},
      s->v());
}

std::shared_ptr<Chain::chain>
insert_chain(const std::shared_ptr<Ascii::ascii> &c,
             const std::shared_ptr<String::string> &s1,
             const std::shared_ptr<String::string> &s2,
             const std::shared_ptr<Nat::nat> &n,
             const std::shared_ptr<Chain::chain> &c0) {
  return Chain::chain::ctor::change_(
      s1, String::string::ctor::String_(c, s1),
      String::string::ctor::String_(c, s2), n,
      Edit::edit::ctor::insertion_(c, s1),
      Chain::chain::ctor::skip_(c, s1, s2, n, c0));
}

std::shared_ptr<Chain::chain>
inserts_chain_empty(const std::shared_ptr<String::string> &s) {
  return std::visit(
      Overloaded{[](const typename String::string::EmptyString _args) -> T1 {
                   return Chain::chain::ctor::empty_();
                 },
                 [](const typename String::string::String _args) -> T1 {
                   std::shared_ptr<Ascii::ascii> a = _args._a0;
                   std::shared_ptr<String::string> s0 = _args._a1;
                   return insert_chain(a, String::string::ctor::EmptyString_(),
                                       s0, length(s0), inserts_chain_empty(s0));
                 }},
      s->v());
}

std::shared_ptr<Chain::chain>
delete_chain(const std::shared_ptr<Ascii::ascii> &c,
             const std::shared_ptr<String::string> &s1,
             const std::shared_ptr<String::string> &s2,
             const std::shared_ptr<Nat::nat> &n,
             const std::shared_ptr<Chain::chain> &c0) {
  return Chain::chain::ctor::change_(String::string::ctor::String_(c, s1), s1,
                                     s2, n, Edit::edit::ctor::deletion_(c, s1),
                                     c0);
}

std::shared_ptr<Chain::chain>
deletes_chain_empty(const std::shared_ptr<String::string> &s) {
  return std::visit(
      Overloaded{[](const typename String::string::EmptyString _args) -> T1 {
                   return Chain::chain::ctor::empty_();
                 },
                 [](const typename String::string::String _args) -> T1 {
                   std::shared_ptr<Ascii::ascii> a = _args._a0;
                   std::shared_ptr<String::string> s0 = _args._a1;
                   return delete_chain(a, s0,
                                       String::string::ctor::EmptyString_(),
                                       length(s0), deletes_chain_empty(s0));
                 }},
      s->v());
}

std::shared_ptr<Chain::chain>
update_chain(const std::shared_ptr<Ascii::ascii> &c,
             const std::shared_ptr<Ascii::ascii> &c_,
             const std::shared_ptr<String::string> &s1,
             const std::shared_ptr<String::string> &s2,
             const std::shared_ptr<Nat::nat> &n,
             const std::shared_ptr<Chain::chain> &c0) {
  return Chain::chain::ctor::change_(
      String::string::ctor::String_(c, s1),
      String::string::ctor::String_(c_, s1),
      String::string::ctor::String_(c_, s2), n,
      Edit::edit::ctor::update_(c, c_, s1),
      Chain::chain::ctor::skip_(c_, s1, s2, n, c0));
}

std::shared_ptr<Chain::chain>
aux_insert(const std::shared_ptr<String::string> &_x,
           const std::shared_ptr<String::string> &_x0,
           const std::shared_ptr<Ascii::ascii> &x,
           const std::shared_ptr<String::string> &xs,
           const std::shared_ptr<Ascii::ascii> &y,
           const std::shared_ptr<String::string> &ys,
           const std::shared_ptr<Nat::nat> &n,
           const std::shared_ptr<Chain::chain> &r1) {
  return insert_chain(y, String::string::ctor::String_(x, xs), ys, n, r1);
}

std::shared_ptr<Chain::chain>
aux_delete(const std::shared_ptr<String::string> &_x,
           const std::shared_ptr<String::string> &_x0,
           const std::shared_ptr<Ascii::ascii> &x,
           const std::shared_ptr<String::string> &xs,
           const std::shared_ptr<Ascii::ascii> &y,
           const std::shared_ptr<String::string> &ys,
           const std::shared_ptr<Nat::nat> &n,
           const std::shared_ptr<Chain::chain> &r2) {
  return delete_chain(x, xs, String::string::ctor::String_(y, ys), n, r2);
}

std::shared_ptr<Chain::chain>
aux_update(const std::shared_ptr<String::string> &_x,
           const std::shared_ptr<String::string> &_x0,
           const std::shared_ptr<Ascii::ascii> &x,
           const std::shared_ptr<String::string> &xs,
           const std::shared_ptr<Ascii::ascii> &y,
           const std::shared_ptr<String::string> &ys,
           const std::shared_ptr<Nat::nat> &n,
           const std::shared_ptr<Chain::chain> &r3) {
  return update_chain(x, y, xs, ys, n, r3);
}

std::shared_ptr<Chain::chain>
aux_eq_char(const std::shared_ptr<String::string> &_x,
            const std::shared_ptr<String::string> &_x0,
            const std::shared_ptr<Ascii::ascii> &_x1,
            const std::shared_ptr<String::string> &xs,
            const std::shared_ptr<Ascii::ascii> &y,
            const std::shared_ptr<String::string> &ys,
            const std::shared_ptr<Nat::nat> &n,
            const std::shared_ptr<Chain::chain> &c) {
  return Chain::chain::ctor::skip_(y, xs, ys, n, c);
}

std::shared_ptr<Chain::chain>
aux_both_empty(const std::shared_ptr<String::string> &_x,
               const std::shared_ptr<String::string> &_x0) {
  return Chain::chain::ctor::empty_();
}

std::shared_ptr<
    SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>>
levenshtein_chain(const std::shared_ptr<String::string> &s,
                  const std::shared_ptr<String::string> &_x0) {
  std::function<std::shared_ptr<
      SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>>(
      std::shared_ptr<String::string>)>
      levenshtein_chain1;
  levenshtein_chain1 =
      [&](std::
              shared_ptr<String::string>
                  t) -> std::
                         shared_ptr<SigT::sigT<std::shared_ptr<Nat::nat>,
                                               std::shared_ptr<Chain::chain>>> {
                           return std::visit(
                               Overloaded{
                                   [&](const typename String::string::
                                           EmptyString _args)
                                       -> std::function<
                                           std::shared_ptr<SigT::sigT<
                                               std::shared_ptr<Nat::nat>,
                                               std::shared_ptr<Chain::chain>>>(
                                               dummy_prop, dummy_prop)> {
                                     return std::visit(
                                         Overloaded{
                                             [&](const typename String::string::
                                                     EmptyString _args)
                                                 -> std::function<
                                                     std::shared_ptr<SigT::sigT<
                                                         std::shared_ptr<
                                                             Nat::nat>,
                                                         std::shared_ptr<
                                                             Chain::chain>>>(
                                                         dummy_prop,
                                                         dummy_prop)> {
                                               return SigT::sigT<
                                                   std::shared_ptr<Nat::nat>,
                                                   std::shared_ptr<
                                                       Chain::chain>>::ctor::
                                                   existT_(
                                                       Nat::nat::ctor::O_(),
                                                       aux_both_empty(s, t));
                                             },
                                             [&](const typename String::string::
                                                     String _args)
                                                 -> std::function<
                                                     std::shared_ptr<SigT::sigT<
                                                         std::shared_ptr<
                                                             Nat::nat>,
                                                         std::shared_ptr<
                                                             Chain::chain>>>(
                                                         dummy_prop,
                                                         dummy_prop)> {
                                               return SigT::sigT<
                                                   std::shared_ptr<Nat::nat>,
                                                   std::shared_ptr<
                                                       Chain::chain>>::ctor::
                                                   existT_(
                                                       length(t),
                                                       inserts_chain_empty(t));
                                             }},
                                         t->v());
                                   },
                                   [&](const typename String::string::
                                           String
                                               _args) -> std::
                                                          function<std::shared_ptr<
                                                              SigT::sigT<
                                                                  std::shared_ptr<
                                                                      Nat::nat>,
                                                                  std::shared_ptr<
                                                                      Chain::
                                                                          chain>>>(
                                                              dummy_prop,
                                                              dummy_prop)> {
                                                            std::shared_ptr<
                                                                Ascii::ascii>
                                                                x = _args._a0;
                                                            std::shared_ptr<
                                                                String::string>
                                                                xs = _args._a1;
                                                            return std::visit(
                                                                Overloaded{
                                                                    [&](const typename String::
                                                                            string::EmptyString
                                                                                _args)
                                                                        -> std::function<std::shared_ptr<
                                                                            SigT::sigT<
                                                                                std::shared_ptr<
                                                                                    Nat::
                                                                                        nat>,
                                                                                std::shared_ptr<
                                                                                    Chain::
                                                                                        chain>>>(
                                                                            dummy_prop,
                                                                            dummy_prop)> {
                                                                      return SigT::sigT<
                                                                          std::shared_ptr<
                                                                              Nat::
                                                                                  nat>,
                                                                          std::shared_ptr<
                                                                              Chain::
                                                                                  chain>>::
                                                                          ctor::existT_(
                                                                              length(
                                                                                  s),
                                                                              deletes_chain_empty(
                                                                                  String::string::
                                                                                      ctor::String_(
                                                                                          x,
                                                                                          xs)));
                                                                    },
                                                                    [&](const typename String::
                                                                            string::String
                                                                                _args)
                                                                        -> std::function<std::shared_ptr<
                                                                            SigT::
                                                                                sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::
                                                                                                                                    chain>>>(dummy_prop, dummy_prop)> {
                                                                      std::shared_ptr<
                                                                          Ascii::
                                                                              ascii>
                                                                          y = _args
                                                                                  ._a0;
                                                                      std::shared_ptr<
                                                                          String::
                                                                              string>
                                                                          ys =
                                                                              _args
                                                                                  ._a1;
                                                                      return std::
                                                                          visit(
                                                                              Overloaded{
                                                                                  [&](const typename Sumbool::
                                                                                          sumbool::left
                                                                                              _args) -> std::
                                                                                                         shared_ptr<SigT::sigT<
                                                                                                             std::shared_ptr<
                                                                                                                 Nat::
                                                                                                                     nat>,
                                                                                                             std::shared_ptr<
                                                                                                                 Chain::
                                                                                                                     chain>>> {
                                                                                                           return std::visit(
                                                                                                               Overloaded{
                                                                                                                   [&](const typename SigT::sigT<
                                                                                                                       std::shared_ptr<
                                                                                                                           Nat::
                                                                                                                               nat>,
                                                                                                                       std::shared_ptr<
                                                                                                                           Chain::
                                                                                                                               chain>>::
                                                                                                                           existT
                                                                                                                               _args)
                                                                                                                       -> std::shared_ptr<SigT::sigT<
                                                                                                                           std::shared_ptr<
                                                                                                                               Nat::
                                                                                                                                   nat>,
                                                                                                                           std::shared_ptr<
                                                                                                                               Chain::
                                                                                                                                   chain>>> {
                                                                                                                     std::shared_ptr<
                                                                                                                         Nat::
                                                                                                                             nat>
                                                                                                                         n = _args
                                                                                                                                 ._a0;
                                                                                                                     std::shared_ptr<
                                                                                                                         Chain::
                                                                                                                             chain>
                                                                                                                         c = _args
                                                                                                                                 ._a1;
                                                                                                                     return SigT::sigT<
                                                                                                                         std::shared_ptr<
                                                                                                                             Nat::
                                                                                                                                 nat>,
                                                                                                                         std::shared_ptr<
                                                                                                                             Chain::
                                                                                                                                 chain>>::
                                                                                                                         ctor::existT_(
                                                                                                                             n,
                                                                                                                             aux_eq_char(
                                                                                                                                 s,
                                                                                                                                 t,
                                                                                                                                 x,
                                                                                                                                 xs,
                                                                                                                                 y,
                                                                                                                                 ys,
                                                                                                                                 n,
                                                                                                                                 c));
                                                                                                                   }},
                                                                                                               levenshtein_chain(
                                                                                                                   xs,
                                                                                                                   ys)
                                                                                                                   ->v());
                                                                                                         },
                                                                                  [&](const typename Sumbool::
                                                                                          sumbool::right
                                                                                              _args)
                                                                                      -> std::shared_ptr<SigT::sigT<
                                                                                          std::shared_ptr<
                                                                                              Nat::
                                                                                                  nat>,
                                                                                          std::shared_ptr<
                                                                                              Chain::
                                                                                                  chain>>> {
                                                                                    return std::visit(
                                                                                        Overloaded{
                                                                                            [&](const typename SigT::sigT<
                                                                                                std::shared_ptr<
                                                                                                    Nat::
                                                                                                        nat>,
                                                                                                std::shared_ptr<
                                                                                                    Chain::
                                                                                                        chain>>::
                                                                                                    existT
                                                                                                        _args)
                                                                                                -> std::shared_ptr<SigT::sigT<
                                                                                                    std::shared_ptr<
                                                                                                        Nat::
                                                                                                            nat>,
                                                                                                    std::shared_ptr<
                                                                                                        Chain::
                                                                                                            chain>>> {
                                                                                              std::shared_ptr<
                                                                                                  Nat::
                                                                                                      nat>
                                                                                                  n1 =
                                                                                                      _args
                                                                                                          ._a0;
                                                                                              std::shared_ptr<
                                                                                                  Chain::
                                                                                                      chain>
                                                                                                  r1 =
                                                                                                      _args
                                                                                                          ._a1;
                                                                                              return std::visit(
                                                                                                  Overloaded{
                                                                                                      [&](const typename SigT::sigT<
                                                                                                          std::shared_ptr<
                                                                                                              Nat::
                                                                                                                  nat>,
                                                                                                          std::shared_ptr<
                                                                                                              Chain::
                                                                                                                  chain>>::
                                                                                                              existT
                                                                                                                  _args)
                                                                                                          -> std::shared_ptr<SigT::sigT<
                                                                                                              std::shared_ptr<
                                                                                                                  Nat::
                                                                                                                      nat>,
                                                                                                              std::shared_ptr<
                                                                                                                  Chain::
                                                                                                                      chain>>> {
                                                                                                        std::shared_ptr<
                                                                                                            Nat::
                                                                                                                nat>
                                                                                                            n2 =
                                                                                                                _args
                                                                                                                    ._a0;
                                                                                                        std::shared_ptr<
                                                                                                            Chain::
                                                                                                                chain>
                                                                                                            r2 =
                                                                                                                _args
                                                                                                                    ._a1;
                                                                                                        return std::visit(
                                                                                                            Overloaded{
                                                                                                                [&](const typename SigT::sigT<
                                                                                                                    std::shared_ptr<
                                                                                                                        Nat::
                                                                                                                            nat>,
                                                                                                                    std::shared_ptr<
                                                                                                                        Chain::
                                                                                                                            chain>>::
                                                                                                                        existT
                                                                                                                            _args)
                                                                                                                    -> std::
                                                                                                                        shared_ptr<SigT::sigT<
                                                                                                                            std::shared_ptr<
                                                                                                                                Nat::
                                                                                                                                    nat>,
                                                                                                                            std::shared_ptr<
                                                                                                                                Chain::
                                                                                                                                    chain>>> {
                                                                                                                          std::shared_ptr<
                                                                                                                              Nat::
                                                                                                                                  nat>
                                                                                                                              n3 =
                                                                                                                                  _args
                                                                                                                                      ._a0;
                                                                                                                          std::shared_ptr<
                                                                                                                              Chain::
                                                                                                                                  chain>
                                                                                                                              r3 =
                                                                                                                                  _args
                                                                                                                                      ._a1;
                                                                                                                          std::shared_ptr<
                                                                                                                              Chain::
                                                                                                                                  chain>
                                                                                                                              r1_ = aux_insert(
                                                                                                                                  s,
                                                                                                                                  t,
                                                                                                                                  x,
                                                                                                                                  xs,
                                                                                                                                  y,
                                                                                                                                  ys,
                                                                                                                                  n1,
                                                                                                                                  r1);
                                                                                                                          std::shared_ptr<
                                                                                                                              Chain::
                                                                                                                                  chain>
                                                                                                                              r2_ = aux_delete(
                                                                                                                                  s,
                                                                                                                                  t,
                                                                                                                                  x,
                                                                                                                                  xs,
                                                                                                                                  y,
                                                                                                                                  ys,
                                                                                                                                  n2,
                                                                                                                                  r2);
                                                                                                                          std::shared_ptr<
                                                                                                                              Chain::
                                                                                                                                  chain>
                                                                                                                              r3_ = aux_update(
                                                                                                                                  s,
                                                                                                                                  t,
                                                                                                                                  x,
                                                                                                                                  xs,
                                                                                                                                  y,
                                                                                                                                  ys,
                                                                                                                                  n3,
                                                                                                                                  r3);
                                                                                                                          return min3_app<
                                                                                                                              std::shared_ptr<
                                                                                                                                  SigT::
                                                                                                                                      sigT<std::shared_ptr<Nat::nat>, std::
                                                                                                                                                                          shared_ptr<
                                                                                                                                                                              Chain::
                                                                                                                                                                                  chain>>>>(SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>::ctor::existT_(Nat::nat::ctor::S_(n1), r1_), SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>::ctor::existT_(Nat::nat::ctor::S_(n2), r2_), SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<Chain::chain>>::ctor::existT_(Nat::nat::ctor::S_(n3), r3_), projT1<std::shared_ptr<Nat::nat>>);
                                                                                                                        }},
                                                                                                            levenshtein_chain(
                                                                                                                xs,
                                                                                                                ys)
                                                                                                                ->v());
                                                                                                      }},
                                                                                                  levenshtein_chain(
                                                                                                      xs,
                                                                                                      String::string::
                                                                                                          ctor::String_(
                                                                                                              y,
                                                                                                              ys))
                                                                                                      ->v());
                                                                                            }},
                                                                                        levenshtein_chain1(
                                                                                            ys)
                                                                                            ->v());
                                                                                  }},
                                                                              ascii_dec(
                                                                                  x,
                                                                                  y)
                                                                                  ->v());
                                                                    }},
                                                                t->v());
                                                          }},
                               s->v());
                         };
  return levenshtein_chain1(_x0);
}
