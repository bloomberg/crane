#include <epoch_cell_glyph_trace.h>

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

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return add(y, Positive::xo(mul(_args.d_a0, y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::xo(mul(_args.d_a0, std::move(y)));
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
            return std::visit(
                Overloaded{
                    [](const typename Positive::XI _args0) -> Comparison {
                      return Comparison::e_LT;
                    },
                    [](const typename Positive::XO _args0) -> Comparison {
                      return Comparison::e_LT;
                    },
                    [&](const typename Positive::XH _args0) -> Comparison {
                      return r;
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

__attribute__((pure)) bool Pos::eqb(const std::shared_ptr<Positive> &p,
                                    const std::shared_ptr<Positive> &q) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> bool {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0) -> bool {
                             return eqb(_args.d_a0, _args0.d_a0);
                           },
                           [](const typename Positive::XO _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return false;
                           }},
                q->v());
          },
          [&](const typename Positive::XO _args) -> bool {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0) -> bool {
                             return false;
                           },
                           [&](const typename Positive::XO _args0) -> bool {
                             return eqb(_args.d_a0, _args0.d_a0);
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return false;
                           }},
                q->v());
          },
          [&](const typename Positive::XH _args) -> bool {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XO _args0) -> bool {
                             return false;
                           },
                           [](const typename Positive::XH _args0) -> bool {
                             return true;
                           }},
                q->v());
          }},
      p->v());
}

__attribute__((pure)) unsigned int
Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
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
            if (std::move(y).use_count() == 1 &&
                std::move(y)->v().index() == 1) {
              auto &_rf = std::get<1>(std::move(y)->v_mut());
              std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
              _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
              return std::move(y);
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
                  std::move(y)->v());
            }
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            if (std::move(y).use_count() == 1 &&
                std::move(y)->v().index() == 2) {
              auto &_rf = std::get<2>(std::move(y)->v_mut());
              std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
              _rf.d_a0 = Pos::add(std::move(_args.d_a0), y_);
              return std::move(y);
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
                  std::move(y)->v());
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
                Overloaded{[](const typename Z::Z0 _args0) -> Comparison {
                             return Comparison::e_GT;
                           },
                           [&](const typename Z::Zpos _args0) -> Comparison {
                             return Pos::compare(_args.d_a0, _args0.d_a0);
                           },
                           [](const typename Z::Zneg _args0) -> Comparison {
                             return Comparison::e_GT;
                           }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args0) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [](const typename Z::Zpos _args0) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [&](const typename Z::Zneg _args0) -> Comparison {
                             return Datatypes::CompOpp(
                                 Pos::compare(_args.d_a0, _args0.d_a0));
                           }},
                y->v());
          }},
      x->v());
}

__attribute__((pure)) bool BinInt::leb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_EQ: {
    return true;
  }
  case Comparison::e_LT: {
    return true;
  }
  case Comparison::e_GT: {
    return false;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool BinInt::ltb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::e_EQ: {
    return false;
  }
  case Comparison::e_LT: {
    return true;
  }
  case Comparison::e_GT: {
    return false;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool BinInt::eqb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return true; },
                    [](const typename Z::Zpos _args0) -> bool { return false; },
                    [](const typename Z::Zneg _args0) -> bool {
                      return false;
                    }},
                y->v());
          },
          [&](const typename Z::Zpos _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return false; },
                    [&](const typename Z::Zpos _args0) -> bool {
                      return Pos::eqb(_args.d_a0, _args0.d_a0);
                    },
                    [](const typename Z::Zneg _args0) -> bool {
                      return false;
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> bool { return false; },
                    [](const typename Z::Zpos _args0) -> bool { return false; },
                    [&](const typename Z::Zneg _args0) -> bool {
                      return Pos::eqb(_args.d_a0, _args0.d_a0);
                    }},
                y->v());
          }},
      x->v());
}

__attribute__((pure)) unsigned int BinInt::to_nat(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{
          [](const typename Z::Z0 _args) -> unsigned int { return 0u; },
          [](const typename Z::Zpos _args) -> unsigned int {
            return Pos::to_nat(_args.d_a0);
          },
          [](const typename Z::Zneg _args) -> unsigned int { return 0u; }},
      z->v());
}

__attribute__((pure)) std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
BinInt::pos_div_eucl(const std::shared_ptr<Positive> &a, std::shared_ptr<Z> b) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            std::shared_ptr<Z> q = BinInt::pos_div_eucl(_args.d_a0, b).first;
            std::shared_ptr<Z> r = BinInt::pos_div_eucl(_args.d_a0, b).second;
            std::shared_ptr<Z> r_ = BinInt::add(
                BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r),
                Z::zpos(Positive::xh()));
            if (BinInt::ltb(r_, b)) {
              return std::make_pair(
                  BinInt::mul(Z::zpos(Positive::xo(Positive::xh())),
                              std::move(q)),
                  std::move(r_));
            } else {
              return std::make_pair(
                  BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())),
                                          std::move(q)),
                              Z::zpos(Positive::xh())),
                  BinInt::sub(std::move(r_), b));
            }
          },
          [&](const typename Positive::XO _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            std::shared_ptr<Z> q = BinInt::pos_div_eucl(_args.d_a0, b).first;
            std::shared_ptr<Z> r = BinInt::pos_div_eucl(_args.d_a0, b).second;
            std::shared_ptr<Z> r_ =
                BinInt::mul(Z::zpos(Positive::xo(Positive::xh())), r);
            if (BinInt::ltb(r_, b)) {
              return std::make_pair(
                  BinInt::mul(Z::zpos(Positive::xo(Positive::xh())),
                              std::move(q)),
                  std::move(r_));
            } else {
              return std::make_pair(
                  BinInt::add(BinInt::mul(Z::zpos(Positive::xo(Positive::xh())),
                                          std::move(q)),
                              Z::zpos(Positive::xh())),
                  BinInt::sub(std::move(r_), b));
            }
          },
          [&](const typename Positive::XH _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            if (BinInt::leb(Z::zpos(Positive::xo(Positive::xh())),
                            std::move(b))) {
              return std::make_pair(Z::z0(), Z::zpos(Positive::xh()));
            } else {
              return std::make_pair(Z::zpos(Positive::xh()), Z::z0());
            }
          }},
      a->v());
}

__attribute__((pure)) std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
BinInt::div_eucl(std::shared_ptr<Z> a, std::shared_ptr<Z> b) {
  return std::visit(
      Overloaded{
          [](const typename Z::Z0 _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            return std::make_pair(Z::z0(), Z::z0());
          },
          [&](const typename Z::Zpos _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            return std::visit(
                Overloaded{
                    [&](const typename Z::Z0 _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      return std::make_pair(Z::z0(), std::move(a));
                    },
                    [&](const typename Z::Zpos _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      return BinInt::pos_div_eucl(_args.d_a0, std::move(b));
                    },
                    [&](const typename Z::Zneg _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      std::shared_ptr<Z> q =
                          BinInt::pos_div_eucl(_args.d_a0, Z::zpos(_args0.d_a0))
                              .first;
                      std::shared_ptr<Z> r =
                          BinInt::pos_div_eucl(_args.d_a0, Z::zpos(_args0.d_a0))
                              .second;
                      return std::visit(
                          Overloaded{[&](const typename Z::Z0 _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(BinInt::opp(q),
                                                             Z::z0());
                                     },
                                     [&](const typename Z::Zpos _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(
                                           BinInt::opp(BinInt::add(
                                               q, Z::zpos(Positive::xh()))),
                                           BinInt::add(b, r));
                                     },
                                     [&](const typename Z::Zneg _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(
                                           BinInt::opp(BinInt::add(
                                               q, Z::zpos(Positive::xh()))),
                                           BinInt::add(b, r));
                                     }},
                          r->v());
                    }},
                b->v());
          },
          [&](const typename Z::Zneg _args)
              -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
            return std::visit(
                Overloaded{
                    [&](const typename Z::Z0 _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      return std::make_pair(Z::z0(), std::move(a));
                    },
                    [&](const typename Z::Zpos _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      std::shared_ptr<Z> q =
                          BinInt::pos_div_eucl(_args.d_a0, b).first;
                      std::shared_ptr<Z> r =
                          BinInt::pos_div_eucl(_args.d_a0, b).second;
                      return std::visit(
                          Overloaded{[&](const typename Z::Z0 _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(BinInt::opp(q),
                                                             Z::z0());
                                     },
                                     [&](const typename Z::Zpos _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(
                                           BinInt::opp(BinInt::add(
                                               q, Z::zpos(Positive::xh()))),
                                           BinInt::sub(b, r));
                                     },
                                     [&](const typename Z::Zneg _args1)
                                         -> std::pair<std::shared_ptr<Z>,
                                                      std::shared_ptr<Z>> {
                                       return std::make_pair(
                                           BinInt::opp(BinInt::add(
                                               q, Z::zpos(Positive::xh()))),
                                           BinInt::sub(b, r));
                                     }},
                          r->v());
                    },
                    [&](const typename Z::Zneg _args0)
                        -> std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>> {
                      std::shared_ptr<Z> q =
                          BinInt::pos_div_eucl(_args.d_a0, Z::zpos(_args0.d_a0))
                              .first;
                      std::shared_ptr<Z> r =
                          BinInt::pos_div_eucl(_args.d_a0, Z::zpos(_args0.d_a0))
                              .second;
                      return std::make_pair(q, BinInt::opp(r));
                    }},
                b->v());
          }},
      a->v());
}

std::shared_ptr<Z> BinInt::div(const std::shared_ptr<Z> &a,
                               const std::shared_ptr<Z> &b) {
  std::shared_ptr<Z> q = BinInt::div_eucl(a, b).first;
  std::shared_ptr<Z> _x = BinInt::div_eucl(a, b).second;
  return q;
}

std::shared_ptr<Z> BinInt::modulo(const std::shared_ptr<Z> &a,
                                  const std::shared_ptr<Z> &b) {
  std::shared_ptr<Z> _x = BinInt::div_eucl(a, b).first;
  std::shared_ptr<Z> r = BinInt::div_eucl(a, b).second;
  return r;
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

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::phase_code(
    const EpochCellGlyphTraceCase::LunarPhase p) {
  switch (p) {
  case LunarPhase::e_NEWMOON: {
    return 0u;
  }
  case LunarPhase::e_FIRSTQUARTER: {
    return 1u;
  }
  case LunarPhase::e_FULLMOON: {
    return 2u;
  }
  case LunarPhase::e_LASTQUARTER: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::phase_from_angle(const std::shared_ptr<Z> &angle_deg) {
  std::shared_ptr<Z> wrapped = BinInt::modulo(
      angle_deg,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(wrapped,
                  Z::zpos(Positive::xi(Positive::xo(Positive::xi(
                      Positive::xi(Positive::xo(Positive::xh())))))))) {
    return LunarPhase::e_NEWMOON;
  } else {
    if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xi(Positive::xi(
                                 Positive::xo(Positive::xo(Positive::xo(
                                     Positive::xo(Positive::xh())))))))))) {
      return LunarPhase::e_FIRSTQUARTER;
    } else {
      if (BinInt::ltb(wrapped, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                   Positive::xo(Positive::xo(Positive::xi(
                                       Positive::xi(Positive::xh())))))))))) {
        return LunarPhase::e_FULLMOON;
      } else {
        if (BinInt::ltb(std::move(wrapped),
                        Z::zpos(Positive::xi(Positive::xi(Positive::xo(
                            Positive::xi(Positive::xi(Positive::xi(Positive::xo(
                                Positive::xo(Positive::xh()))))))))))) {
          return LunarPhase::e_LASTQUARTER;
        } else {
          return LunarPhase::e_NEWMOON;
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::zodiac_code(
    const EpochCellGlyphTraceCase::ZodiacSign z) {
  switch (z) {
  case ZodiacSign::e_ARIES: {
    return 0u;
  }
  case ZodiacSign::e_TAURUS: {
    return 1u;
  }
  case ZodiacSign::e_GEMINI: {
    return 2u;
  }
  case ZodiacSign::e_CANCER: {
    return 3u;
  }
  case ZodiacSign::e_LEO: {
    return 4u;
  }
  case ZodiacSign::e_VIRGO: {
    return 5u;
  }
  case ZodiacSign::e_LIBRA: {
    return 6u;
  }
  case ZodiacSign::e_SCORPIO: {
    return 7u;
  }
  case ZodiacSign::e_SAGITTARIUS: {
    return 8u;
  }
  case ZodiacSign::e_CAPRICORN: {
    return 9u;
  }
  case ZodiacSign::e_AQUARIUS: {
    return 10u;
  }
  case ZodiacSign::e_PISCES: {
    return 11u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::eclipse_possible_at_dial(
    const std::shared_ptr<Z> &dial_pos) {
  if (BinInt::eqb(dial_pos, Z::zpos(Positive::xh()))) {
    return true;
  } else {
    if (BinInt::eqb(dial_pos,
                    Z::zpos(Positive::xo(Positive::xi(Positive::xh()))))) {
      return true;
    } else {
      if (BinInt::eqb(dial_pos, Z::zpos(Positive::xo(Positive::xo(
                                    Positive::xi(Positive::xh())))))) {
        return true;
      } else {
        if (BinInt::eqb(dial_pos,
                        Z::zpos(Positive::xi(Positive::xo(
                            Positive::xo(Positive::xo(Positive::xh()))))))) {
          return true;
        } else {
          return false;
        }
      }
    }
  }
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step(
    std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> s) {
  return std::make_shared<
      EpochCellGlyphTraceCase::MechanismState>(MechanismState{
      BinInt::add(s->crank_position, Z::zpos(Positive::xh())),
      BinInt::modulo(BinInt::add(s->metonic_dial, Z::zpos(Positive::xh())),
                     metonic_modulus),
      BinInt::modulo(BinInt::add(s->saros_dial, Z::zpos(Positive::xh())),
                     saros_modulus),
      BinInt::modulo(BinInt::add(s->callippic_dial, Z::zpos(Positive::xh())),
                     callippic_modulus),
      BinInt::modulo(BinInt::add(s->exeligmos_dial, Z::zpos(Positive::xh())),
                     exeligmos_modulus),
      BinInt::modulo(BinInt::add(s->games_dial, Z::zpos(Positive::xh())),
                     games_modulus),
      BinInt::modulo(BinInt::add(s->zodiac_position, Z::zpos(Positive::xh())),
                     zodiac_modulus)});
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step_reverse(
    std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> s) {
  return std::make_shared<EpochCellGlyphTraceCase::MechanismState>(
      MechanismState{
          BinInt::sub(s->crank_position, Z::zpos(Positive::xh())),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->metonic_dial, Z::zpos(Positive::xh())),
                          metonic_modulus),
              metonic_modulus),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->saros_dial, Z::zpos(Positive::xh())),
                          saros_modulus),
              saros_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->callippic_dial,
                                                 Z::zpos(Positive::xh())),
                                     callippic_modulus),
                         callippic_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->exeligmos_dial,
                                                 Z::zpos(Positive::xh())),
                                     exeligmos_modulus),
                         exeligmos_modulus),
          BinInt::modulo(
              BinInt::add(BinInt::sub(s->games_dial, Z::zpos(Positive::xh())),
                          games_modulus),
              games_modulus),
          BinInt::modulo(BinInt::add(BinInt::sub(s->zodiac_position,
                                                 Z::zpos(Positive::xh())),
                                     zodiac_modulus),
                         zodiac_modulus)});
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::step_n(
    const unsigned int n,
    std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> s) {
  if (n <= 0) {
    return std::move(s);
  } else {
    unsigned int rest = n - 1;
    return step_n(std::move(rest), step(s));
  }
}

std::shared_ptr<EpochCellGlyphTraceCase::MechanismState>
EpochCellGlyphTraceCase::state_at_cell(std::shared_ptr<Z> cell) {
  return std::make_shared<EpochCellGlyphTraceCase::MechanismState>(
      MechanismState{cell, cell, cell, cell, cell, cell, cell});
}

__attribute__((pure)) EpochCellGlyphTraceCase::LunarPhase
EpochCellGlyphTraceCase::predict_moon_phase_from_state(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  std::shared_ptr<Z> phase_angle = BinInt::div(
      BinInt::mul(s->metonic_dial,
                  Z::zpos(Positive::xo(Positive::xo(
                      Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                          Positive::xi(Positive::xo(Positive::xh())))))))))),
      Z::zpos(Positive::xi(Positive::xi(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xi(Positive::xh())))))))));
  return phase_from_angle(std::move(phase_angle));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::predict_olympiad_year(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  return BinInt::add(
      BinInt::modulo(s->games_dial,
                     Z::zpos(Positive::xo(Positive::xo(Positive::xh())))),
      Z::zpos(Positive::xh()));
}

__attribute__((pure)) EpochCellGlyphTraceCase::ZodiacSign
EpochCellGlyphTraceCase::predict_zodiac_sign(
    const std::shared_ptr<EpochCellGlyphTraceCase::MechanismState> &s) {
  std::shared_ptr<Z> deg = BinInt::modulo(
      s->zodiac_position,
      Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(Positive::xo(
          Positive::xi(Positive::xi(Positive::xo(Positive::xh()))))))))));
  if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(
                           Positive::xi(Positive::xi(Positive::xh()))))))) {
    return ZodiacSign::e_ARIES;
  } else {
    if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                             Positive::xi(Positive::xi(Positive::xh())))))))) {
      return ZodiacSign::e_TAURUS;
    } else {
      if (BinInt::ltb(
              deg, Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xi(
                       Positive::xi(Positive::xo(Positive::xh()))))))))) {
        return ZodiacSign::e_GEMINI;
      } else {
        if (BinInt::ltb(
                deg,
                Z::zpos(Positive::xo(Positive::xo(Positive::xo(Positive::xi(
                    Positive::xi(Positive::xi(Positive::xh()))))))))) {
          return ZodiacSign::e_CANCER;
        } else {
          if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xi(Positive::xi(
                                   Positive::xo(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xh())))))))))) {
            return ZodiacSign::e_LEO;
          } else {
            if (BinInt::ltb(deg, Z::zpos(Positive::xo(Positive::xo(Positive::xi(
                                     Positive::xo(Positive::xi(Positive::xi(
                                         Positive::xo(Positive::xh())))))))))) {
              return ZodiacSign::e_VIRGO;
            } else {
              if (BinInt::ltb(deg,
                              Z::zpos(Positive::xo(Positive::xi(Positive::xo(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xi(Positive::xh())))))))))) {
                return ZodiacSign::e_LIBRA;
              } else {
                if (BinInt::ltb(deg,
                                Z::zpos(Positive::xo(Positive::xo(Positive::xo(
                                    Positive::xo(Positive::xi(Positive::xi(
                                        Positive::xi(Positive::xh())))))))))) {
                  return ZodiacSign::e_SCORPIO;
                } else {
                  if (BinInt::ltb(
                          deg, Z::zpos(Positive::xo(Positive::xi(
                                   Positive::xi(Positive::xi(Positive::xo(
                                       Positive::xo(Positive::xo(Positive::xo(
                                           Positive::xh()))))))))))) {
                    return ZodiacSign::e_SAGITTARIUS;
                  } else {
                    if (BinInt::ltb(
                            deg, Z::zpos(Positive::xo(Positive::xo(
                                     Positive::xi(Positive::xi(Positive::xo(
                                         Positive::xi(Positive::xo(Positive::xo(
                                             Positive::xh()))))))))))) {
                      return ZodiacSign::e_CAPRICORN;
                    } else {
                      if (BinInt::ltb(
                              std::move(deg),
                              Z::zpos(Positive::xo(Positive::xi(
                                  Positive::xo(Positive::xi(Positive::xo(
                                      Positive::xo(Positive::xi(Positive::xo(
                                          Positive::xh()))))))))))) {
                        return ZodiacSign::e_AQUARIUS;
                      } else {
                        return ZodiacSign::e_PISCES;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::eclipse_category_code(
    const EpochCellGlyphTraceCase::EclipseCategory c) {
  switch (c) {
  case EclipseCategory::e_EC_TOTALLUNAR: {
    return 0u;
  }
  case EclipseCategory::e_EC_PARTIALLUNAR: {
    return 1u;
  }
  case EclipseCategory::e_EC_TOTALSOLAR: {
    return 2u;
  }
  case EclipseCategory::e_EC_ANNULARSOLAR: {
    return 3u;
  }
  case EclipseCategory::e_EC_PARTIALSOLAR: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::glyph_code(
    const EpochCellGlyphTraceCase::DialGlyph g) {
  switch (g) {
  case DialGlyph::e_GLYPH_SIGMA: {
    return 0u;
  }
  case DialGlyph::e_GLYPH_ETA: {
    return 1u;
  }
  case DialGlyph::e_GLYPH_SIGMATOTAL: {
    return 2u;
  }
  case DialGlyph::e_GLYPH_ETAANNULAR: {
    return 3u;
  }
  case DialGlyph::e_GLYPH_EMPTY: {
    return 4u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::category_matches_glyph(
    const EpochCellGlyphTraceCase::EclipseCategory cat,
    const EpochCellGlyphTraceCase::DialGlyph g) {
  switch (cat) {
  case EclipseCategory::e_EC_TOTALLUNAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return true;
    }
    case DialGlyph::e_GLYPH_ETA: {
      return false;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return true;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return false;
    }
    case DialGlyph::e_GLYPH_EMPTY: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case EclipseCategory::e_EC_PARTIALLUNAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return true;
    }
    case DialGlyph::e_GLYPH_ETA: {
      return false;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return false;
    }
    case DialGlyph::e_GLYPH_EMPTY: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case EclipseCategory::e_EC_TOTALSOLAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETA: {
      return true;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return false;
    }
    case DialGlyph::e_GLYPH_EMPTY: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case EclipseCategory::e_EC_ANNULARSOLAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETA: {
      return true;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return true;
    }
    case DialGlyph::e_GLYPH_EMPTY: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  case EclipseCategory::e_EC_PARTIALSOLAR: {
    switch (g) {
    case DialGlyph::e_GLYPH_SIGMA: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETA: {
      return true;
    }
    case DialGlyph::e_GLYPH_SIGMATOTAL: {
      return false;
    }
    case DialGlyph::e_GLYPH_ETAANNULAR: {
      return false;
    }
    case DialGlyph::e_GLYPH_EMPTY: {
      return false;
    }
    default:
      std::unreachable();
    }
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) EpochCellGlyphTraceCase::DialGlyph
EpochCellGlyphTraceCase::glyph_at_cell(const std::shared_ptr<Z> &cell) {
  if (BinInt::eqb(cell, Z::z0())) {
    return DialGlyph::e_GLYPH_SIGMATOTAL;
  } else {
    if (BinInt::eqb(cell,
                    Z::zpos(Positive::xo(Positive::xi(Positive::xh()))))) {
      return DialGlyph::e_GLYPH_SIGMA;
    } else {
      if (BinInt::eqb(cell, Z::zpos(Positive::xo(
                                Positive::xo(Positive::xi(Positive::xh())))))) {
        return DialGlyph::e_GLYPH_ETA;
      } else {
        if (BinInt::eqb(cell, Z::zpos(Positive::xi(Positive::xo(Positive::xo(
                                  Positive::xo(Positive::xh()))))))) {
          return DialGlyph::e_GLYPH_SIGMA;
        } else {
          return DialGlyph::e_GLYPH_EMPTY;
        }
      }
    }
  }
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::count_total_lunar(
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons
                 _args) -> unsigned int {
            unsigned int count_here = [&]() {
              switch (_args.d_a0->he_category) {
              case EclipseCategory::e_EC_TOTALLUNAR: {
                return 1u;
              }
              case EclipseCategory::e_EC_PARTIALLUNAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_TOTALSOLAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_ANNULARSOLAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_PARTIALSOLAR: {
                return 0u;
              }
              default:
                std::unreachable();
              }
            }();
            return (std::move(count_here) + count_total_lunar(_args.d_a1));
          }},
      es->v());
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::count_visible_total_lunar(
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons
                 _args) -> unsigned int {
            unsigned int count_here = [&]() {
              switch (_args.d_a0->he_category) {
              case EclipseCategory::e_EC_TOTALLUNAR: {
                if (_args.d_a0->he_visible_mediterranean) {
                  return 1u;
                } else {
                  return 0u;
                }
              }
              case EclipseCategory::e_EC_PARTIALLUNAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_TOTALSOLAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_ANNULARSOLAR: {
                return 0u;
              }
              case EclipseCategory::e_EC_PARTIALSOLAR: {
                return 0u;
              }
              default:
                std::unreachable();
              }
            }();
            return (std::move(count_here) +
                    count_visible_total_lunar(_args.d_a1));
          }},
      es->v());
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::visible_series_checksum(
    const std::shared_ptr<
        List<std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>>
        &es) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Nil
                 _args) -> unsigned int { return 0u; },
          [](const typename List<
              std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse>>::Cons
                 _args) -> unsigned int {
            unsigned int term;
            if (_args.d_a0->he_visible_mediterranean) {
              term = BinInt::to_nat(BinInt::abs(_args.d_a0->he_saros_series));
            } else {
              term = 0u;
            }
            return (std::move(term) + visible_series_checksum(_args.d_a1));
          }},
      es->v());
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::months_from_epoch(
    const std::shared_ptr<Z> &epoch_year,
    const std::shared_ptr<Z> &eclipse_year,
    const std::shared_ptr<Z> &epoch_month,
    const std::shared_ptr<Z> &eclipse_month) {
  std::shared_ptr<Z> year_diff = BinInt::sub(epoch_year, eclipse_year);
  std::shared_ptr<Z> month_diff = BinInt::sub(eclipse_month, epoch_month);
  return BinInt::add(
      BinInt::mul(std::move(year_diff), Z::zpos(Positive::xo(Positive::xo(
                                            Positive::xi(Positive::xh()))))),
      std::move(month_diff));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::saros_cell(
    const std::shared_ptr<Z> &epoch_year, const std::shared_ptr<Z> &epoch_month,
    const std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse> &e) {
  std::shared_ptr<Z> months =
      months_from_epoch(epoch_year, e->he_year, epoch_month, e->he_month);
  return BinInt::modulo(
      std::move(months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

std::shared_ptr<Z> EpochCellGlyphTraceCase::saros_dial_at_month(
    const std::shared_ptr<Z> &start_cell, const std::shared_ptr<Z> &months) {
  return BinInt::modulo(
      BinInt::add(start_cell, months),
      Z::zpos(Positive::xi(Positive::xi(Positive::xi(Positive::xi(
          Positive::xi(Positive::xo(Positive::xi(Positive::xh())))))))));
}

std::shared_ptr<EpochCellGlyphTraceCase::EpochReading>
EpochCellGlyphTraceCase::build_epoch_reading(
    const std::shared_ptr<Z> &epoch_year, const std::shared_ptr<Z> &epoch_month,
    std::shared_ptr<EpochCellGlyphTraceCase::HistoricalEclipse> e) {
  std::shared_ptr<Z> cell = saros_cell(epoch_year, epoch_month, e);
  return std::make_shared<EpochCellGlyphTraceCase::EpochReading>(EpochReading{
      state_at_cell(cell), std::move(e), cell, glyph_at_cell(cell)});
}

__attribute__((pure)) bool EpochCellGlyphTraceCase::reading_matches(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return category_matches_glyph(reading->reading_eclipse->he_category,
                                reading->reading_glyph);
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_phase_code(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return phase_code(predict_moon_phase_from_state(reading->reading_state));
}

__attribute__((pure)) unsigned int EpochCellGlyphTraceCase::reading_zodiac_code(
    const std::shared_ptr<EpochCellGlyphTraceCase::EpochReading> &reading) {
  return zodiac_code(predict_zodiac_sign(reading->reading_state));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::phase_code_after_steps(const unsigned int n) {
  return phase_code(predict_moon_phase_from_state(step_n(n, initial_state)));
}

__attribute__((pure)) unsigned int
EpochCellGlyphTraceCase::zodiac_code_after_steps(const unsigned int n) {
  return zodiac_code(predict_zodiac_sign(step_n(n, initial_state)));
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

__attribute__((pure)) bool QArith_base::Qle_bool(std::shared_ptr<Q> x,
                                                 std::shared_ptr<Q> y) {
  return BinInt::leb(BinInt::mul(x->Qnum, Z::zpos(y->Qden)),
                     BinInt::mul(y->Qnum, Z::zpos(x->Qden)));
}
