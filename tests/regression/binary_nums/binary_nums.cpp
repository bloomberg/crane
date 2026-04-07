#include <binary_nums.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Positive> Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::xo(succ(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xi(_args.d_a0);
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xo(Positive::xh());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(_args.d_a0);
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(Overloaded{[](const typename Positive::XI _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(
                                               succ(_args0.d_a0));
                                         },
                                         [](const typename Positive::XO _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xi(_args0.d_a0);
                                         },
                                         [](const typename Positive::XH _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(Positive::xh());
                                         }},
                              y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add_carry(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XO _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xo(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XH _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(succ(_args.d_a0));
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(Positive::xh());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::xi(Positive::xo(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xi(pred_double(_args.d_a0));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xh();
          }},
      x->v());
}

std::shared_ptr<N> Pos::pred_N(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::XI _args) -> std::shared_ptr<N> {
                   return N::npos(Positive::xo(_args.d_a0));
                 },
                 [](const typename Positive::XO _args) -> std::shared_ptr<N> {
                   return N::npos(pred_double(_args.d_a0));
                 },
                 [](const typename Positive::XH _args) -> std::shared_ptr<N> {
                   return N::n0();
                 }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{[](const typename Pos::mask::IsNul _args)
                     -> std::shared_ptr<Pos::mask> {
                   return mask::ispos(Positive::xh());
                 },
                 [](const typename Pos::mask::IsPos _args)
                     -> std::shared_ptr<Pos::mask> {
                   return mask::ispos(Positive::xi(_args.d_a0));
                 },
                 [](const typename Pos::mask::IsNeg _args)
                     -> std::shared_ptr<Pos::mask> { return mask::isneg(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{[](const typename Pos::mask::IsNul _args)
                     -> std::shared_ptr<Pos::mask> { return mask::isnul(); },
                 [](const typename Pos::mask::IsPos _args)
                     -> std::shared_ptr<Pos::mask> {
                   return mask::ispos(Positive::xo(_args.d_a0));
                 },
                 [](const typename Pos::mask::IsNeg _args)
                     -> std::shared_ptr<Pos::mask> { return mask::isneg(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Pos::mask> {
            return mask::ispos(Positive::xo(Positive::xo(_args.d_a0)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            return mask::ispos(Positive::xo(pred_double(_args.d_a0)));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return mask::isnul();
          }},
      x->v());
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return succ_double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ispos(Positive::xo(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ispos(pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::XH _args0)
                        -> std::shared_ptr<Pos::mask> { return mask::isnul(); },
                    [](const auto _args0) -> std::shared_ptr<Pos::mask> {
                      return mask::isneg();
                    }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::sub_mask_carry(const std::shared_ptr<Positive> &x,
                    const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ispos(pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Pos::mask> {
                             return double_pred_mask(_args.d_a0);
                           }},
                y->v());
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return mask::isneg();
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return add(y, Positive::xo(mul(_args.d_a0, y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xo(mul(_args.d_a0, y));
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::move(y);
          }},
      x->v());
}

__attribute__((pure)) Comparison
Pos::compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
                  const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> Comparison {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0) -> Comparison {
                      return compare_cont(r, _args.d_a0, _args0.d_a0);
                    },
                    [&](const typename Positive::XO _args0) -> Comparison {
                      return compare_cont(Comparison::e_GT, _args.d_a0,
                                          _args0.d_a0);
                    },
                    [](const typename Positive::XH _args0) -> Comparison {
                      return Comparison::e_GT;
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> Comparison {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0) -> Comparison {
                      return compare_cont(Comparison::e_LT, _args.d_a0,
                                          _args0.d_a0);
                    },
                    [&](const typename Positive::XO _args0) -> Comparison {
                      return compare_cont(r, _args.d_a0, _args0.d_a0);
                    },
                    [](const typename Positive::XH _args0) -> Comparison {
                      return Comparison::e_GT;
                    }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> Comparison {
            return std::visit(Overloaded{[&](const typename Positive::XH _args0)
                                             -> Comparison { return r; },
                                         [](const auto _args0) -> Comparison {
                                           return Comparison::e_LT;
                                         }},
                              y->v());
          }},
      x->v());
}

__attribute__((pure)) Comparison
Pos::compare(const std::shared_ptr<Positive> &_x0,
             const std::shared_ptr<Positive> &_x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
}

__attribute__((pure)) unsigned int
Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<Positive> Coq_Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::xo(succ(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xi(_args.d_a0);
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xo(Positive::xh());
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(_args.d_a0);
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(Overloaded{[](const typename Positive::XI _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(
                                               succ(_args0.d_a0));
                                         },
                                         [](const typename Positive::XO _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xi(_args0.d_a0);
                                         },
                                         [](const typename Positive::XH _args0)
                                             -> std::shared_ptr<Positive> {
                                           return Positive::xo(Positive::xh());
                                         }},
                              y->v());
          }},
      x->v());
}

std::shared_ptr<Positive>
Coq_Pos::add_carry(const std::shared_ptr<Positive> &x,
                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XO _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xo(add_carry(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XH _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::xi(succ(_args.d_a0));
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xo(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::xi(Positive::xh());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return add(y, Positive::xo(mul(_args.d_a0, y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xo(mul(_args.d_a0, y));
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::move(y);
          }},
      x->v());
}

__attribute__((pure)) unsigned int
Coq_Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<N> BinNat::sub(std::shared_ptr<N> n,
                               const std::shared_ptr<N> &m) {
  if (n.use_count() == 1 && n->v().index() == 0) {
    auto &_rf = std::get<0>(n->v_mut());
    return n;
  } else {
    return std::visit(
        Overloaded{
            [](const typename N::N0 _args) -> std::shared_ptr<N> {
              return N::n0();
            },
            [&](const typename N::Npos _args) -> std::shared_ptr<N> {
              return std::visit(
                  Overloaded{
                      [&](const typename N::N0 _args0) -> std::shared_ptr<N> {
                        return std::move(n);
                      },
                      [&](const typename N::Npos _args0) -> std::shared_ptr<N> {
                        return std::visit(
                            Overloaded{
                                [](const typename Pos::mask::IsPos _args1)
                                    -> std::shared_ptr<N> {
                                  return N::npos(_args1.d_a0);
                                },
                                [](const auto _args1) -> std::shared_ptr<N> {
                                  return N::n0();
                                }},
                            Pos::sub_mask(_args.d_a0, _args0.d_a0)->v());
                      }},
                  m->v());
            }},
        n->v());
  }
}

__attribute__((pure)) Comparison BinNat::compare(const std::shared_ptr<N> &n,
                                                 const std::shared_ptr<N> &m) {
  return std::visit(
      Overloaded{
          [&](const typename N::N0 _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename N::N0 _args0) -> Comparison {
                             return Comparison::e_EQ;
                           },
                           [](const typename N::Npos _args0) -> Comparison {
                             return Comparison::e_LT;
                           }},
                m->v());
          },
          [&](const typename N::Npos _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename N::N0 _args0) -> Comparison {
                             return Comparison::e_GT;
                           },
                           [&](const typename N::Npos _args0) -> Comparison {
                             return Pos::compare(_args.d_a0, _args0.d_a0);
                           }},
                m->v());
          }},
      n->v());
}

std::shared_ptr<N> BinNat::pred(const std::shared_ptr<N> &n) {
  return std::visit(
      Overloaded{[](const typename N::N0 _args) -> std::shared_ptr<N> {
                   return N::n0();
                 },
                 [](const typename N::Npos _args) -> std::shared_ptr<N> {
                   return Pos::pred_N(_args.d_a0);
                 }},
      n->v());
}

std::shared_ptr<N> BinNat::add(std::shared_ptr<N> n, std::shared_ptr<N> m) {
  return std::visit(
      Overloaded{
          [&](const typename N::N0 _args) -> std::shared_ptr<N> {
            return std::move(m);
          },
          [&](const typename N::Npos _args) -> std::shared_ptr<N> {
            if (m.use_count() == 1 && m->v().index() == 1) {
              auto &_rf = std::get<1>(m->v_mut());
              std::shared_ptr<Positive> q = std::move(_rf.d_a0);
              _rf.d_a0 = Coq_Pos::add(std::move(_args.d_a0), q);
              return m;
            } else {
              return std::visit(
                  Overloaded{
                      [&](const typename N::N0 _args0) -> std::shared_ptr<N> {
                        return std::move(n);
                      },
                      [&](const typename N::Npos _args0) -> std::shared_ptr<N> {
                        return N::npos(Coq_Pos::add(_args.d_a0, _args0.d_a0));
                      }},
                  m->v());
            }
          }},
      n->v());
}

std::shared_ptr<N> BinNat::mul(const std::shared_ptr<N> &n,
                               const std::shared_ptr<N> &m) {
  return std::visit(
      Overloaded{
          [](const typename N::N0 _args) -> std::shared_ptr<N> {
            return N::n0();
          },
          [&](const typename N::Npos _args) -> std::shared_ptr<N> {
            return std::visit(
                Overloaded{
                    [](const typename N::N0 _args0) -> std::shared_ptr<N> {
                      return N::n0();
                    },
                    [&](const typename N::Npos _args0) -> std::shared_ptr<N> {
                      return N::npos(Coq_Pos::mul(_args.d_a0, _args0.d_a0));
                    }},
                m->v());
          }},
      n->v());
}

__attribute__((pure)) unsigned int BinNat::to_nat(const std::shared_ptr<N> &a) {
  return std::visit(
      Overloaded{[](const typename N::N0 _args) -> unsigned int { return 0u; },
                 [](const typename N::Npos _args) -> unsigned int {
                   return Pos::to_nat(_args.d_a0);
                 }},
      a->v());
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xo(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xo(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xh());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xi(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Pos::pred_double(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xh());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Pos::pred_double(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xi(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::double_(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::succ_double(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zpos(Positive::xo(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::pred_double(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return BinInt::double_(
                                 BinInt::pos_sub(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zpos(Pos::pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zneg(Positive::xo(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Z> {
                             return Z::zneg(Pos::pred_double(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Z> { return Z::z0(); }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Z> BinInt::add(std::shared_ptr<Z> x, std::shared_ptr<Z> y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
            return std::move(y);
          },
          [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
            if (y.use_count() == 1 && y->v().index() == 1) {
              auto &_rf = std::get<1>(y->v_mut());
              std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
              _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
              return y;
            } else {
              return std::visit(
                  Overloaded{
                      [&](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                        return std::move(x);
                      },
                      [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                        return Z::zpos(Pos::add(_args.d_a0, _args0.d_a0));
                      },
                      [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                        return BinInt::pos_sub(_args.d_a0, _args0.d_a0);
                      }},
                  y->v());
            }
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            if (y.use_count() == 1 && y->v().index() == 2) {
              auto &_rf = std::get<2>(y->v_mut());
              std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
              _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
              return y;
            } else {
              return std::visit(
                  Overloaded{
                      [&](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                        return std::move(x);
                      },
                      [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                        return BinInt::pos_sub(_args0.d_a0, _args.d_a0);
                      },
                      [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                        return Z::zneg(Pos::add(_args.d_a0, _args0.d_a0));
                      }},
                  y->v());
            }
          }},
      x->v());
}

std::shared_ptr<Z> BinInt::opp(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zneg(_args.d_a0);
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zpos(_args.d_a0);
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::sub(const std::shared_ptr<Z> &m,
                               const std::shared_ptr<Z> &n) {
  return BinInt::add(m, BinInt::opp(n));
}

std::shared_ptr<Z> BinInt::mul(const std::shared_ptr<Z> &x,
                               const std::shared_ptr<Z> &y) {
  return std::visit(
      Overloaded{
          [](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
            return Z::z0();
          },
          [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                      return Z::z0();
                    },
                    [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                      return Z::zpos(Pos::mul(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                      return Z::zneg(Pos::mul(_args.d_a0, _args0.d_a0));
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                      return Z::z0();
                    },
                    [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                      return Z::zneg(Pos::mul(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                      return Z::zpos(Pos::mul(_args.d_a0, _args0.d_a0));
                    }},
                y->v());
          }},
      x->v());
}

__attribute__((pure)) Comparison BinInt::compare(const std::shared_ptr<Z> &x,
                                                 const std::shared_ptr<Z> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args0) -> Comparison {
                             return Comparison::e_EQ;
                           },
                           [](const typename Z::Zpos _args0) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [](const typename Z::Zneg _args0) -> Comparison {
                             return Comparison::e_GT;
                           }},
                y->v());
          },
          [&](const typename Z::Zpos _args) -> Comparison {
            return std::visit(
                Overloaded{[&](const typename Z::Zpos _args0) -> Comparison {
                             return Pos::compare(_args.d_a0, _args0.d_a0);
                           },
                           [](const auto _args0) -> Comparison {
                             return Comparison::e_GT;
                           }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> Comparison {
            return std::visit(
                Overloaded{[&](const typename Z::Zneg _args0) -> Comparison {
                             return Datatypes::CompOpp(
                                 Pos::compare(_args.d_a0, _args0.d_a0));
                           },
                           [](const auto _args0) -> Comparison {
                             return Comparison::e_LT;
                           }},
                y->v());
          }},
      x->v());
}

__attribute__((pure)) unsigned int BinInt::to_nat(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Zpos _args) -> unsigned int {
                   return Pos::to_nat(_args.d_a0);
                 },
                 [](const auto _args) -> unsigned int { return 0u; }},
      z->v());
}

std::shared_ptr<Z> BinInt::abs(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(_args.d_a0);
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zpos(_args.d_a0);
                 }},
      z->v());
}

std::shared_ptr<N> BinaryNums::n_max(std::shared_ptr<N> a,
                                     std::shared_ptr<N> b) {
  switch (BinNat::compare(a, b)) {
  case Comparison::e_LT: {
    return std::move(b);
  }
  default: {
    return std::move(a);
  }
  }
}

std::shared_ptr<Z> BinaryNums::z_sign(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::zpos(Positive::xh());
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xh());
                 }},
      z->v());
}

__attribute__((pure)) Comparison Datatypes::CompOpp(const Comparison r) {
  switch (r) {
  case Comparison::e_EQ: {
    return Comparison::e_EQ;
  }
  case Comparison::e_LT: {
    return Comparison::e_GT;
  }
  case Comparison::e_GT: {
    return Comparison::e_LT;
  }
  default:
    std::unreachable();
  }
}
