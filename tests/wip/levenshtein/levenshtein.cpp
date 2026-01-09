#include <functional>
#include <iostream>
#include <levenshtein.h>
#include <memory>
#include <string>
#include <variant>

std::shared_ptr<typename Bool0::bool0>
leb(const std::shared_ptr<typename Nat::nat> n,
    const std::shared_ptr<typename Nat::nat> m) {
  return std::visit(
      Overloaded{[&](const typename Nat::O _args)
                     -> std::shared_ptr<typename Bool0::bool0> {
                   return Bool0::true0::make();
                 },
                 [&](const typename Nat::S _args)
                     -> std::shared_ptr<typename Bool0::bool0> {
                   std::shared_ptr<typename Nat::nat> n_ = _args._a0;
                   return std::visit(
                       Overloaded{
                           [&](const typename Nat::O _args)
                               -> std::shared_ptr<typename Bool0::bool0> {
                             return Bool0::false0::make();
                           },
                           [&](const typename Nat::S _args)
                               -> std::shared_ptr<typename Bool0::bool0> {
                             std::shared_ptr<typename Nat::nat> m_ = _args._a0;
                             return leb(n_, m_);
                           }},
                       *m);
                 }},
      *n);
}

std::shared_ptr<typename Sumbool::sumbool>
bool_dec(const std::shared_ptr<typename Bool0::bool0> b1,
         const std::shared_ptr<typename Bool0::bool0> b2) {
  return std::visit(
      Overloaded{
          [&](const typename Bool0::true0 _args) -> T1 {
            return std::visit(
                Overloaded{[&](const typename Bool0::true0 _args)
                               -> std::shared_ptr<typename Sumbool::sumbool> {
                             return Sumbool::left::make();
                           },
                           [&](const typename Bool0::false0 _args)
                               -> std::shared_ptr<typename Sumbool::sumbool> {
                             return Sumbool::right::make();
                           }},
                *b2);
          },
          [&](const typename Bool0::false0 _args) -> T1 {
            return std::visit(
                Overloaded{[&](const typename Bool0::true0 _args)
                               -> std::shared_ptr<typename Sumbool::sumbool> {
                             return Sumbool::right::make();
                           },
                           [&](const typename Bool0::false0 _args)
                               -> std::shared_ptr<typename Sumbool::sumbool> {
                             return Sumbool::left::make();
                           }},
                *b2);
          }},
      *b1);
}

std::shared_ptr<typename Sumbool::sumbool>
ascii_dec(const std::shared_ptr<typename Ascii::ascii> a,
          const std::shared_ptr<typename Ascii::ascii> b) {
  return std::visit(
      Overloaded{
          [&](const typename Ascii::Ascii _args) -> T1 {
            std::shared_ptr<typename Bool0::bool0> b0 = _args._a0;
            std::shared_ptr<typename Bool0::bool0> b1 = _args._a1;
            std::shared_ptr<typename Bool0::bool0> b2 = _args._a2;
            std::shared_ptr<typename Bool0::bool0> b3 = _args._a3;
            std::shared_ptr<typename Bool0::bool0> b4 = _args._a4;
            std::shared_ptr<typename Bool0::bool0> b5 = _args._a5;
            std::shared_ptr<typename Bool0::bool0> b6 = _args._a6;
            std::shared_ptr<typename Bool0::bool0> b7 = _args._a7;
            return std::visit(Overloaded{[&](const typename Ascii::Ascii
                                                 _args) -> std::
                                                            shared_ptr<
                                                                typename Sumbool::
                                                                    sumbool> {
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b8 =
                                                                      _args._a0;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b9 =
                                                                      _args._a1;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b10 =
                                                                      _args._a2;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b11 =
                                                                      _args._a3;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b12 =
                                                                      _args._a4;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b13 =
                                                                      _args._a5;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b14 =
                                                                      _args._a6;
                                                              std::shared_ptr<
                                                                  typename Bool0::
                                                                      bool0>
                                                                  b15 =
                                                                      _args._a7;
                                                              return std::visit(Overloaded{[&](const typename Sumbool::left _args) -> T1 {
                                                                                             return std::visit(
                                                                                                 Overloaded{
                                                                                                     [&](const typename Sumbool::
                                                                                                             left
                                                                                                                 _args)
                                                                                                         -> T1 {
                                                                                                       return std::visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                            left
                                                                                                                                                _args)
                                                                                                                                        -> T1 {
                                                                                                                                      return std::visit(
                                                                                                                                          Overloaded{
                                                                                                                                              [&](const typename Sumbool::
                                                                                                                                                      left
                                                                                                                                                          _args)
                                                                                                                                                  -> T1 {
                                                                                                                                                return std::visit(Overloaded{
                                                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                                                              left
                                                                                                                                                                                  _args)
                                                                                                                                                                          -> T1 {
                                                                                                                                                                        return std::
                                                                                                                                                                            visit(Overloaded{
                                                                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                                                                              left
                                                                                                                                                                                                  _args)
                                                                                                                                                                                          -> T1 {
                                                                                                                                                                                        return std::
                                                                                                                                                                                            visit(Overloaded{[&](const typename Sumbool::
                                                                                                                                                                                                                     left
                                                                                                                                                                                                                         _args)
                                                                                                                                                                                                                 -> T1 {
                                                                                                                                                                                                               return std::visit(Overloaded{
                                                                                                                                                                                                                                     [&](const typename Sumbool::
                                                                                                                                                                                                                                             left
                                                                                                                                                                                                                                                 _args)
                                                                                                                                                                                                                                         -> T1 {
                                                                                                                                                                                                                                       return Sumbool::
                                                                                                                                                                                                                                           left::
                                                                                                                                                                                                                                               make();
                                                                                                                                                                                                                                     },
                                                                                                                                                                                                                                     [&](const typename Sumbool::right _args) -> T1 {
                                                                                                                                                                                                                                       return Sumbool::
                                                                                                                                                                                                                                           right::
                                                                                                                                                                                                                                               make();
                                                                                                                                                                                                                                     }},
                                                                                                                                                                                                                                 *bool_dec(
                                                                                                                                                                                                                                     b7,
                                                                                                                                                                                                                                     b15));
                                                                                                                                                                                                             },
                                                                                                                                                                                                             [&](const typename Sumbool::
                                                                                                                                                                                                                     right
                                                                                                                                                                                                                         _args)
                                                                                                                                                                                                                 -> T1 {
                                                                                                                                                                                                               return Sumbool::
                                                                                                                                                                                                                   right::
                                                                                                                                                                                                                       make();
                                                                                                                                                                                                             }},
                                                                                                                                                                                                  *bool_dec(
                                                                                                                                                                                                      b6,
                                                                                                                                                                                                      b14));
                                                                                                                                                                                      },
                                                                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                                                                              right
                                                                                                                                                                                                  _args) -> T1 {
                                                                                                                                                                                        return Sumbool::
                                                                                                                                                                                            right::
                                                                                                                                                                                                make();
                                                                                                                                                                                      }},
                                                                                                                                                                                  *bool_dec(
                                                                                                                                                                                      b5,
                                                                                                                                                                                      b13));
                                                                                                                                                                      },
                                                                                                                                                                      [&](const typename Sumbool::
                                                                                                                                                                              right
                                                                                                                                                                                  _args)
                                                                                                                                                                          -> T1 {
                                                                                                                                                                        return Sumbool::
                                                                                                                                                                            right::
                                                                                                                                                                                make();
                                                                                                                                                                      }},
                                                                                                                                                                  *bool_dec(
                                                                                                                                                                      b4,
                                                                                                                                                                      b12));
                                                                                                                                              },
                                                                                                                                              [&](const typename Sumbool::
                                                                                                                                                      right
                                                                                                                                                          _args)
                                                                                                                                                  -> T1 {
                                                                                                                                                return Sumbool::
                                                                                                                                                    right::
                                                                                                                                                        make();
                                                                                                                                              }},
                                                                                                                                          *bool_dec(
                                                                                                                                              b3,
                                                                                                                                              b11));
                                                                                                                                    },
                                                                                                                                    [&](const typename Sumbool::
                                                                                                                                            right
                                                                                                                                                _args)
                                                                                                                                        -> T1 {
                                                                                                                                      return Sumbool::
                                                                                                                                          right::
                                                                                                                                              make();
                                                                                                                                    }},
                                                                                                                         *bool_dec(
                                                                                                                             b2,
                                                                                                                             b10));
                                                                                                     },
                                                                                                     [&](const typename Sumbool::
                                                                                                             right
                                                                                                                 _args)
                                                                                                         -> T1 {
                                                                                                       return Sumbool::
                                                                                                           right::
                                                                                                               make();
                                                                                                     }},
                                                                                                 *bool_dec(
                                                                                                     b1,
                                                                                                     b9));
                                                                                           },
                                                                                           [&](const typename Sumbool::
                                                                                                   right
                                                                                                       _args)
                                                                                               -> T1 {
                                                                                             return Sumbool::
                                                                                                 right::
                                                                                                     make();
                                                                                           }},
                                                                                *bool_dec(
                                                                                    b0,
                                                                                    b8));
                                                            }},
                              *b);
          }},
      *a);
}

std::shared_ptr<typename Nat::nat>
length(const std::shared_ptr<typename String::string> s) {
  return std::visit(Overloaded{[&](const typename String::EmptyString _args)
                                   -> std::shared_ptr<typename Nat::nat> {
                                 return Nat::O::make();
                               },
                               [&](const typename String::String _args)
                                   -> std::shared_ptr<typename Nat::nat> {
                                 std::shared_ptr<typename String::string> s_ =
                                     _args._a1;
                                 return Nat::S::make(length(s_));
                               }},
                    *s);
}

std::shared_ptr<typename Chain::chain>
insert_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0) {
  return Chain::change::make(
      s1, String::String::make(c, s1), String::String::make(c, s2), n,
      Edit::insertion::make(c, s1), Chain::skip::make(c, s1, s2, n, c0));
}

std::shared_ptr<typename Chain::chain>
inserts_chain_empty(const std::shared_ptr<typename String::string> s) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString _args) -> T1 {
                   return Chain::empty::make();
                 },
                 [&](const typename String::String _args) -> T1 {
                   std::shared_ptr<typename Ascii::ascii> a = _args._a0;
                   std::shared_ptr<typename String::string> s0 = _args._a1;
                   return insert_chain(a, String::EmptyString::make(), s0,
                                       length(s0), inserts_chain_empty(s0));
                 }},
      *s);
}

std::shared_ptr<typename Chain::chain>
delete_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0) {
  return Chain::change::make(String::String::make(c, s1), s1, s2, n,
                             Edit::deletion::make(c, s1), c0);
}

std::shared_ptr<typename Chain::chain>
deletes_chain_empty(const std::shared_ptr<typename String::string> s) {
  return std::visit(
      Overloaded{[&](const typename String::EmptyString _args) -> T1 {
                   return Chain::empty::make();
                 },
                 [&](const typename String::String _args) -> T1 {
                   std::shared_ptr<typename Ascii::ascii> a = _args._a0;
                   std::shared_ptr<typename String::string> s0 = _args._a1;
                   return delete_chain(a, s0, String::EmptyString::make(),
                                       length(s0), deletes_chain_empty(s0));
                 }},
      *s);
}

std::shared_ptr<typename Chain::chain>
update_chain(const std::shared_ptr<typename Ascii::ascii> c,
             const std::shared_ptr<typename Ascii::ascii> c_,
             const std::shared_ptr<typename String::string> s1,
             const std::shared_ptr<typename String::string> s2,
             const std::shared_ptr<typename Nat::nat> n,
             const std::shared_ptr<typename Chain::chain> c0) {
  return Chain::change::make(
      String::String::make(c, s1), String::String::make(c_, s1),
      String::String::make(c_, s2), n, Edit::update::make(c, c_, s1),
      Chain::skip::make(c_, s1, s2, n, c0));
}

std::shared_ptr<typename Chain::chain>
aux_insert(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r1) {
  return insert_chain(y, String::String::make(x, xs), ys, n, r1);
}

std::shared_ptr<typename Chain::chain>
aux_delete(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r2) {
  return delete_chain(x, xs, String::String::make(y, ys), n, r2);
}

std::shared_ptr<typename Chain::chain>
aux_update(const std::shared_ptr<typename String::string> _x,
           const std::shared_ptr<typename String::string> _x0,
           const std::shared_ptr<typename Ascii::ascii> x,
           const std::shared_ptr<typename String::string> xs,
           const std::shared_ptr<typename Ascii::ascii> y,
           const std::shared_ptr<typename String::string> ys,
           const std::shared_ptr<typename Nat::nat> n,
           const std::shared_ptr<typename Chain::chain> r3) {
  return update_chain(x, y, xs, ys, n, r3);
}

std::shared_ptr<typename Chain::chain>
aux_eq_char(const std::shared_ptr<typename String::string> _x,
            const std::shared_ptr<typename String::string> _x0,
            const std::shared_ptr<typename Ascii::ascii> _x1,
            const std::shared_ptr<typename String::string> xs,
            const std::shared_ptr<typename Ascii::ascii> y,
            const std::shared_ptr<typename String::string> ys,
            const std::shared_ptr<typename Nat::nat> n,
            const std::shared_ptr<typename Chain::chain> c) {
  return Chain::skip::make(y, xs, ys, n, c);
}

std::shared_ptr<typename Chain::chain>
aux_both_empty(const std::shared_ptr<typename String::string> _x,
               const std::shared_ptr<typename String::string> _x0) {
  return Chain::empty::make();
}

std::shared_ptr<typename SigT::sigT<std::shared_ptr<typename Nat::nat>,
                                    std::shared_ptr<typename Chain::chain>>>
levenshtein_chain(const std::shared_ptr<typename String::string> s,
                  const std::shared_ptr<typename String::string> _x0) {
  std::function<std::shared_ptr<
      typename SigT::sigT<std::shared_ptr<typename Nat::nat>,
                          std::shared_ptr<typename Chain::chain>>>(
      std::shared_ptr<typename String::string>)>
      levenshtein_chain1;
  levenshtein_chain1 = [&](std::shared_ptr<typename String::string> t)
      -> std::shared_ptr<
          typename SigT::sigT<std::shared_ptr<typename Nat::nat>,
                              std::shared_ptr<typename Chain::chain>>> {
    return std::visit(
        Overloaded{
            [&](const typename String::EmptyString _args)
                -> std::function<std::shared_ptr<typename SigT::sigT<
                    std::shared_ptr<typename Nat::nat>,
                    std::shared_ptr<typename Chain::chain>>>(dummy_prop,
                                                             dummy_prop)> {
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString _args)
                          -> std::function<std::shared_ptr<typename SigT::sigT<
                              std::shared_ptr<typename Nat::nat>,
                              std::shared_ptr<typename Chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return SigT::existT<
                            std::shared_ptr<typename Nat::nat>,
                            std::shared_ptr<typename Chain::chain>>::
                            make(Nat::O::make(), aux_both_empty(_x0, t));
                      },
                      [&](const typename String::String _args)
                          -> std::function<std::shared_ptr<typename SigT::sigT<
                              std::shared_ptr<typename Nat::nat>,
                              std::shared_ptr<typename Chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return SigT::existT<
                            std::shared_ptr<typename Nat::nat>,
                            std::shared_ptr<typename Chain::chain>>::
                            make(length(t), inserts_chain_empty(t));
                      }},
                  *t);
            },
            [&](const typename String::String _args)
                -> std::function<std::shared_ptr<typename SigT::sigT<
                    std::shared_ptr<typename Nat::nat>,
                    std::shared_ptr<typename Chain::chain>>>(dummy_prop,
                                                             dummy_prop)> {
              std::shared_ptr<typename Ascii::ascii> x = _args._a0;
              std::shared_ptr<typename String::string> xs = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename String::EmptyString _args)
                          -> std::function<std::shared_ptr<typename SigT::sigT<
                              std::shared_ptr<typename Nat::nat>,
                              std::shared_ptr<typename Chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return SigT::existT<
                            std::shared_ptr<typename Nat::nat>,
                            std::shared_ptr<typename Chain::chain>>::
                            make(length(_x0), deletes_chain_empty(
                                                  String::String::make(x, xs)));
                      },
                      [&](const typename String::String _args)
                          -> std::function<std::shared_ptr<typename SigT::sigT<
                              std::shared_ptr<typename Nat::nat>,
                              std::shared_ptr<typename Chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        std::shared_ptr<typename Ascii::ascii> y = _args._a0;
                        std::shared_ptr<typename String::string> ys = _args._a1;
                        return std::visit(
                            Overloaded{
                                [&](const typename Sumbool::left _args)
                                    -> std::shared_ptr<typename SigT::sigT<
                                        std::shared_ptr<typename Nat::nat>,
                                        std::shared_ptr<
                                            typename Chain::chain>>> {
                                  return std::visit(
                                      Overloaded{
                                          [&](const typename SigT::existT<
                                              std::shared_ptr<
                                                  typename Nat::nat>,
                                              std::shared_ptr<
                                                  typename Chain::chain>>
                                                  _args)
                                              -> std::shared_ptr<
                                                  typename SigT::sigT<
                                                      std::shared_ptr<
                                                          typename Nat::nat>,
                                                      std::shared_ptr<
                                                          typename Chain::
                                                              chain>>> {
                                            std::shared_ptr<typename Nat::nat>
                                                n = _args._a0;
                                            std::shared_ptr<
                                                typename Chain::chain>
                                                c = _args._a1;
                                            return SigT::existT<
                                                std::shared_ptr<
                                                    typename Nat::nat>,
                                                std::shared_ptr<
                                                    typename Chain::chain>>::
                                                make(n,
                                                     aux_eq_char(_x0, t, x, xs,
                                                                 y, ys, n, c));
                                          }},
                                      *levenshtein_chain(xs, ys));
                                },
                                [&](const typename Sumbool::right _args)
                                    -> std::shared_ptr<typename SigT::sigT<
                                        std::shared_ptr<typename Nat::nat>,
                                        std::shared_ptr<
                                            typename Chain::chain>>> {
                                  return std::visit(
                                      Overloaded{[&](const typename SigT::existT<
                                                     std::shared_ptr<
                                                         typename Nat::nat>,
                                                     std::shared_ptr<
                                                         typename Chain::chain>>
                                                         _args)
                                                     -> std::shared_ptr<
                                                         typename SigT::sigT<
                                                             std::shared_ptr<
                                                                 typename Nat::
                                                                     nat>,
                                                             std::shared_ptr<
                                                                 typename Chain::
                                                                     chain>>> {
                                        std::shared_ptr<typename Nat::nat> n1 =
                                            _args._a0;
                                        std::shared_ptr<typename Chain::chain>
                                            r1 = _args._a1;
                                        return std::visit(
                                            Overloaded{
                                                [&](const typename SigT::existT<
                                                    std::shared_ptr<
                                                        typename Nat::nat>,
                                                    std::shared_ptr<
                                                        typename Chain::chain>>
                                                        _args)
                                                    -> std::
                                                        shared_ptr<
                                                            typename SigT::sigT<
                                                                std::shared_ptr<
                                                                    typename Nat::
                                                                        nat>,
                                                                std::shared_ptr<
                                                                    typename Chain::
                                                                        chain>>> {
                                                          std::shared_ptr<
                                                              typename Nat::nat>
                                                              n2 = _args._a0;
                                                          std::shared_ptr<
                                                              typename Chain::
                                                                  chain>
                                                              r2 = _args._a1;
                                                          return std::visit(
                                                              Overloaded{
                                                                  [&](const typename SigT::existT<
                                                                      std::shared_ptr<
                                                                          typename Nat::
                                                                              nat>,
                                                                      std::shared_ptr<
                                                                          typename Chain::
                                                                              chain>>
                                                                          _args)
                                                                      -> std::
                                                                          shared_ptr<typename SigT::
                                                                                         sigT<
                                                                                             std::shared_ptr<
                                                                                                 typename Nat::
                                                                                                     nat>,
                                                                                             std::shared_ptr<
                                                                                                 typename Chain::chain>>> {
                                                                            std::shared_ptr<
                                                                                typename Nat::
                                                                                    nat>
                                                                                n3 =
                                                                                    _args
                                                                                        ._a0;
                                                                            std::shared_ptr<
                                                                                typename Chain::
                                                                                    chain>
                                                                                r3 =
                                                                                    _args
                                                                                        ._a1;
                                                                            std::shared_ptr<
                                                                                typename Chain::
                                                                                    chain>
                                                                                r1_ = aux_insert(
                                                                                    _x0,
                                                                                    t,
                                                                                    x,
                                                                                    xs,
                                                                                    y,
                                                                                    ys,
                                                                                    n1,
                                                                                    r1);
                                                                            std::shared_ptr<
                                                                                typename Chain::
                                                                                    chain>
                                                                                r2_ = aux_delete(
                                                                                    _x0,
                                                                                    t,
                                                                                    x,
                                                                                    xs,
                                                                                    y,
                                                                                    ys,
                                                                                    n2,
                                                                                    r2);
                                                                            std::shared_ptr<
                                                                                typename Chain::
                                                                                    chain>
                                                                                r3_ = aux_update(
                                                                                    _x0,
                                                                                    t,
                                                                                    x,
                                                                                    xs,
                                                                                    y,
                                                                                    ys,
                                                                                    n3,
                                                                                    r3);
                                                                            return min3_app<std::shared_ptr<
                                                                                typename SigT::sigT<
                                                                                    std::shared_ptr<
                                                                                        typename Nat::
                                                                                            nat>,
                                                                                    std::shared_ptr<
                                                                                        typename Chain::
                                                                                            chain>>>>(
                                                                                SigT::existT<
                                                                                    std::shared_ptr<
                                                                                        typename Nat::
                                                                                            nat>,
                                                                                    std::shared_ptr<
                                                                                        typename Chain::
                                                                                            chain>>::
                                                                                    make(
                                                                                        Nat::S::make(
                                                                                            n1),
                                                                                        r1_),
                                                                                SigT::existT<
                                                                                    std::shared_ptr<
                                                                                        typename Nat::
                                                                                            nat>,
                                                                                    std::shared_ptr<
                                                                                        typename Chain::
                                                                                            chain>>::
                                                                                    make(
                                                                                        Nat::S::make(
                                                                                            n2),
                                                                                        r2_),
                                                                                SigT::existT<
                                                                                    std::shared_ptr<
                                                                                        typename Nat::
                                                                                            nat>,
                                                                                    std::shared_ptr<
                                                                                        typename Chain::
                                                                                            chain>>::
                                                                                    make(
                                                                                        Nat::S::make(
                                                                                            n3),
                                                                                        r3_),
                                                                                projT1<std::shared_ptr<
                                                                                    typename Nat::
                                                                                        nat>>);
                                                                          }},
                                                              *levenshtein_chain(
                                                                  xs, ys));
                                                        }},
                                            *levenshtein_chain(
                                                xs,
                                                String::String::make(y, ys)));
                                      }},
                                      *levenshtein_chain1(ys));
                                }},
                            *ascii_dec(x, y));
                      }},
                  *t);
            }},
        *_x0);
  };
  return levenshtein_chain1(_x0);
}
