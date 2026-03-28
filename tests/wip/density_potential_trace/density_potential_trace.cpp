#include <density_potential_trace.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int PeanoNat::add(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int p = n - 1;
    return (PeanoNat::add(std::move(p), m) + 1);
  }
}

__attribute__((pure)) unsigned int PeanoNat::mul(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int p = n - 1;
    return PeanoNat::add(m, PeanoNat::mul(p, m));
  }
}

__attribute__((pure)) unsigned int PeanoNat::pow(const unsigned int n,
                                                 const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return PeanoNat::mul(n, PeanoNat::pow(n, m0));
  }
}

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

__attribute__((pure)) unsigned int
Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<Positive> Pos::of_succ_nat(const unsigned int n) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    unsigned int x = n - 1;
    return succ(of_succ_nat(x));
  }
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

std::shared_ptr<Positive>
Coq_Pos::pred_double(const std::shared_ptr<Positive> &x) {
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

std::shared_ptr<mask>
Coq_Pos::succ_double_mask(const std::shared_ptr<mask> &x) {
  return std::visit(
      Overloaded{[](const typename mask::IsNul _args) -> std::shared_ptr<mask> {
                   return mask::ispos(Positive::xh());
                 },
                 [](const typename mask::IsPos _args) -> std::shared_ptr<mask> {
                   return mask::ispos(Positive::xi(_args.d_a0));
                 },
                 [](const typename mask::IsNeg _args) -> std::shared_ptr<mask> {
                   return mask::isneg();
                 }},
      x->v());
}

std::shared_ptr<mask> Coq_Pos::double_mask(const std::shared_ptr<mask> &x) {
  return std::visit(
      Overloaded{[](const typename mask::IsNul _args) -> std::shared_ptr<mask> {
                   return mask::isnul();
                 },
                 [](const typename mask::IsPos _args) -> std::shared_ptr<mask> {
                   return mask::ispos(Positive::xo(_args.d_a0));
                 },
                 [](const typename mask::IsNeg _args) -> std::shared_ptr<mask> {
                   return mask::isneg();
                 }},
      x->v());
}

std::shared_ptr<mask>
Coq_Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<mask> {
            return mask::ispos(Positive::xo(Positive::xo(_args.d_a0)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<mask> {
            return mask::ispos(Positive::xo(pred_double(_args.d_a0)));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<mask> {
            return mask::isnul();
          }},
      x->v());
}

std::shared_ptr<mask> Coq_Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                        const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<mask> {
                             return succ_double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<mask> {
                             return mask::ispos(Positive::xo(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<mask> {
                             return mask::ispos(pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<mask> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::XI _args0)
                        -> std::shared_ptr<mask> { return mask::isneg(); },
                    [](const typename Positive::XO _args0)
                        -> std::shared_ptr<mask> { return mask::isneg(); },
                    [](const typename Positive::XH _args0)
                        -> std::shared_ptr<mask> { return mask::isnul(); }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<mask>
Coq_Pos::sub_mask_carry(const std::shared_ptr<Positive> &x,
                        const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<mask> {
                             return double_mask(
                                 sub_mask(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<mask> {
                             return mask::ispos(pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<mask> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<mask> {
                             return double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<mask> {
                             return succ_double_mask(
                                 sub_mask_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<mask> {
                             return double_pred_mask(_args.d_a0);
                           }},
                y->v());
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<mask> {
            return mask::isneg();
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::sub(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [](const typename mask::IsNul _args) -> std::shared_ptr<Positive> {
            return Positive::xh();
          },
          [](const typename mask::IsPos _args) -> std::shared_ptr<Positive> {
            return _args.d_a0;
          },
          [](const typename mask::IsNeg _args) -> std::shared_ptr<Positive> {
            return Positive::xh();
          }},
      sub_mask(x, y)->v());
}

std::shared_ptr<Positive> Coq_Pos::mul(const std::shared_ptr<Positive> &x,
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
Coq_Pos::compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
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
Coq_Pos::compare(const std::shared_ptr<Positive> &_x0,
                 const std::shared_ptr<Positive> &_x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
}

__attribute__((pure)) unsigned int
Coq_Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<Positive> Coq_Pos::pow(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &_x0) {
  return iter<std::shared_ptr<Positive>>(
      [&](const std::shared_ptr<Positive> &_x0) -> std::shared_ptr<Positive> {
        return mul(x, _x0);
      },
      Positive::xh(), _x0);
}

__attribute__((pure)) unsigned int
Coq_Pos::size_nat(const std::shared_ptr<Positive> &p) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> unsigned int {
            return (size_nat(_args.d_a0) + 1);
          },
          [](const typename Positive::XO _args) -> unsigned int {
            return (size_nat(_args.d_a0) + 1);
          },
          [](const typename Positive::XH _args) -> unsigned int { return 1u; }},
      p->v());
}

__attribute__((pure))
std::pair<std::shared_ptr<Positive>,
          std::pair<std::shared_ptr<Positive>, std::shared_ptr<Positive>>>
Coq_Pos::ggcdn(const unsigned int n, std::shared_ptr<Positive> a,
               std::shared_ptr<Positive> b) {
  if (n <= 0) {
    return std::make_pair(Positive::xh(),
                          std::make_pair(std::move(a), std::move(b)));
  } else {
    unsigned int n0 = n - 1;
    return std::visit(
        Overloaded{
            [&](const typename Positive::XI _args)
                -> std::pair<std::shared_ptr<Positive>,
                             std::pair<std::shared_ptr<Positive>,
                                       std::shared_ptr<Positive>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename Positive::XI _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        return [&](void) {
                          switch (compare(_args.d_a0, _args0.d_a0)) {
                          case Comparison::e_EQ: {
                            return std::make_pair(
                                a,
                                std::make_pair(Positive::xh(), Positive::xh()));
                          }
                          case Comparison::e_LT: {
                            std::shared_ptr<Positive> g =
                                ggcdn(n0, sub(_args0.d_a0, _args.d_a0), a)
                                    .first;
                            std::pair<std::shared_ptr<Positive>,
                                      std::shared_ptr<Positive>>
                                p = ggcdn(n0, sub(_args0.d_a0, _args.d_a0), a)
                                        .second;
                            std::shared_ptr<Positive> ba = p.first;
                            std::shared_ptr<Positive> aa = p.second;
                            return std::make_pair(
                                std::move(g),
                                std::make_pair(aa, add(aa, Positive::xo(ba))));
                          }
                          case Comparison::e_GT: {
                            std::shared_ptr<Positive> g =
                                ggcdn(n0, sub(_args.d_a0, _args0.d_a0), b)
                                    .first;
                            std::pair<std::shared_ptr<Positive>,
                                      std::shared_ptr<Positive>>
                                p = ggcdn(n0, sub(_args.d_a0, _args0.d_a0), b)
                                        .second;
                            std::shared_ptr<Positive> ab = p.first;
                            std::shared_ptr<Positive> bb = p.second;
                            return std::make_pair(
                                std::move(g),
                                std::make_pair(add(bb, Positive::xo(ab)), bb));
                          }
                          }
                        }();
                      },
                      [&](const typename Positive::XO _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        std::shared_ptr<Positive> g =
                            ggcdn(n0, a, _args0.d_a0).first;
                        std::pair<std::shared_ptr<Positive>,
                                  std::shared_ptr<Positive>>
                            p = ggcdn(n0, a, _args0.d_a0).second;
                        std::shared_ptr<Positive> aa = p.first;
                        std::shared_ptr<Positive> bb = p.second;
                        return std::make_pair(
                            std::move(g), std::make_pair(aa, Positive::xo(bb)));
                      },
                      [&](const typename Positive::XH _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        return std::make_pair(
                            Positive::xh(), std::make_pair(a, Positive::xh()));
                      }},
                  b->v());
            },
            [&](const typename Positive::XO _args)
                -> std::pair<std::shared_ptr<Positive>,
                             std::pair<std::shared_ptr<Positive>,
                                       std::shared_ptr<Positive>>> {
              return std::visit(
                  Overloaded{
                      [&](const typename Positive::XI _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        std::shared_ptr<Positive> g =
                            ggcdn(n0, _args.d_a0, b).first;
                        std::pair<std::shared_ptr<Positive>,
                                  std::shared_ptr<Positive>>
                            p = ggcdn(n0, _args.d_a0, b).second;
                        std::shared_ptr<Positive> aa = p.first;
                        std::shared_ptr<Positive> bb = p.second;
                        return std::make_pair(
                            std::move(g), std::make_pair(Positive::xo(aa), bb));
                      },
                      [&](const typename Positive::XO _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        std::shared_ptr<Positive> g =
                            ggcdn(n0, _args.d_a0, _args0.d_a0).first;
                        std::pair<std::shared_ptr<Positive>,
                                  std::shared_ptr<Positive>>
                            p = ggcdn(n0, _args.d_a0, _args0.d_a0).second;
                        return std::make_pair(Positive::xo(g), p);
                      },
                      [&](const typename Positive::XH _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        return std::make_pair(
                            Positive::xh(), std::make_pair(a, Positive::xh()));
                      }},
                  b->v());
            },
            [&](const typename Positive::XH _args)
                -> std::pair<std::shared_ptr<Positive>,
                             std::pair<std::shared_ptr<Positive>,
                                       std::shared_ptr<Positive>>> {
              return std::make_pair(
                  Positive::xh(), std::make_pair(Positive::xh(), std::move(b)));
            }},
        a->v());
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<Positive>,
          std::pair<std::shared_ptr<Positive>, std::shared_ptr<Positive>>>
Coq_Pos::ggcd(const std::shared_ptr<Positive> &a,
              const std::shared_ptr<Positive> &b) {
  return ggcdn((size_nat(a) + size_nat(b)), a, b);
}

std::shared_ptr<Positive> Coq_Pos::of_nat(const unsigned int n) {
  if (n <= 0) {
    return Positive::xh();
  } else {
    unsigned int x = n - 1;
    if (x <= 0) {
      return Positive::xh();
    } else {
      unsigned int _x = x - 1;
      return succ(of_nat(x));
    }
  }
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
            return [&](void) {
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
                        [&](const typename Z::Zpos _args0)
                            -> std::shared_ptr<Z> {
                          return Z::zpos(Pos::add(_args.d_a0, _args0.d_a0));
                        },
                        [&](const typename Z::Zneg _args0)
                            -> std::shared_ptr<Z> {
                          return BinInt::pos_sub(_args.d_a0, _args0.d_a0);
                        }},
                    std::move(y)->v());
              }
            }();
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            return [&](void) {
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
                        [&](const typename Z::Zpos _args0)
                            -> std::shared_ptr<Z> {
                          return BinInt::pos_sub(_args0.d_a0, _args.d_a0);
                        },
                        [&](const typename Z::Zneg _args0)
                            -> std::shared_ptr<Z> {
                          return Z::zneg(Pos::add(_args.d_a0, _args0.d_a0));
                        }},
                    std::move(y)->v());
              }
            }();
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
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) bool BinInt::ltb(const std::shared_ptr<Z> &x,
                                       const std::shared_ptr<Z> &y) {
  return [&](void) {
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
    }
  }();
}

std::shared_ptr<Z> BinInt::max(std::shared_ptr<Z> n, std::shared_ptr<Z> m) {
  return [&](void) {
    switch (BinInt::compare(n, m)) {
    case Comparison::e_EQ: {
      return std::move(n);
    }
    case Comparison::e_LT: {
      return std::move(m);
    }
    case Comparison::e_GT: {
      return std::move(n);
    }
    }
  }();
}

std::shared_ptr<Z> BinInt::min(std::shared_ptr<Z> n, std::shared_ptr<Z> m) {
  return [&](void) {
    switch (BinInt::compare(n, m)) {
    case Comparison::e_EQ: {
      return std::move(n);
    }
    case Comparison::e_LT: {
      return std::move(n);
    }
    case Comparison::e_GT: {
      return std::move(m);
    }
    }
  }();
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

std::shared_ptr<Z> BinInt::of_nat(const unsigned int n) {
  if (n <= 0) {
    return Z::z0();
  } else {
    unsigned int n0 = n - 1;
    return Z::zpos(Pos::of_succ_nat(n0));
  }
}

std::shared_ptr<Positive> BinInt::to_pos(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Positive> {
                   return Positive::xh();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Positive> {
                   return _args.d_a0;
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Positive> {
                   return Positive::xh();
                 }},
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

std::shared_ptr<Z> BinInt::sgn(const std::shared_ptr<Z> &z) {
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

__attribute__((pure))
std::pair<std::shared_ptr<Z>, std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>>
BinInt::ggcd(std::shared_ptr<Z> a, std::shared_ptr<Z> b) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args)
              -> std::pair<std::shared_ptr<Z>,
                           std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
            return std::make_pair(BinInt::abs(b),
                                  std::make_pair(Z::z0(), BinInt::sgn(b)));
          },
          [&](const typename Z::Zpos _args)
              -> std::pair<std::shared_ptr<Z>,
                           std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
            return std::visit(
                Overloaded{
                    [&](const typename Z::Z0 _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      return std::make_pair(
                          BinInt::abs(a),
                          std::make_pair(BinInt::sgn(a), Z::z0()));
                    },
                    [&](const typename Z::Zpos _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      std::shared_ptr<Positive> g =
                          Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).first;
                      std::pair<std::shared_ptr<Positive>,
                                std::shared_ptr<Positive>>
                          p = Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).second;
                      std::shared_ptr<Positive> aa = p.first;
                      std::shared_ptr<Positive> bb = p.second;
                      return std::make_pair(
                          Z::zpos(std::move(g)),
                          std::make_pair(Z::zpos(aa), Z::zpos(bb)));
                    },
                    [&](const typename Z::Zneg _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      std::shared_ptr<Positive> g =
                          Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).first;
                      std::pair<std::shared_ptr<Positive>,
                                std::shared_ptr<Positive>>
                          p = Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).second;
                      std::shared_ptr<Positive> aa = p.first;
                      std::shared_ptr<Positive> bb = p.second;
                      return std::make_pair(
                          Z::zpos(std::move(g)),
                          std::make_pair(Z::zpos(aa), Z::zneg(bb)));
                    }},
                std::move(b)->v());
          },
          [&](const typename Z::Zneg _args)
              -> std::pair<std::shared_ptr<Z>,
                           std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
            return std::visit(
                Overloaded{
                    [&](const typename Z::Z0 _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      return std::make_pair(
                          BinInt::abs(a),
                          std::make_pair(BinInt::sgn(a), Z::z0()));
                    },
                    [&](const typename Z::Zpos _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      std::shared_ptr<Positive> g =
                          Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).first;
                      std::pair<std::shared_ptr<Positive>,
                                std::shared_ptr<Positive>>
                          p = Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).second;
                      std::shared_ptr<Positive> aa = p.first;
                      std::shared_ptr<Positive> bb = p.second;
                      return std::make_pair(
                          Z::zpos(std::move(g)),
                          std::make_pair(Z::zneg(aa), Z::zpos(bb)));
                    },
                    [&](const typename Z::Zneg _args0)
                        -> std::pair<
                            std::shared_ptr<Z>,
                            std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>> {
                      std::shared_ptr<Positive> g =
                          Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).first;
                      std::pair<std::shared_ptr<Positive>,
                                std::shared_ptr<Positive>>
                          p = Coq_Pos::ggcd(_args.d_a0, _args0.d_a0).second;
                      std::shared_ptr<Positive> aa = p.first;
                      std::shared_ptr<Positive> bb = p.second;
                      return std::make_pair(
                          Z::zpos(std::move(g)),
                          std::make_pair(Z::zneg(aa), Z::zneg(bb)));
                    }},
                std::move(b)->v());
          }},
      a->v());
}

__attribute__((pure)) DReal
RbaseSymbolsImpl::Rabst(const std::shared_ptr<CReal> &_x0) {
  return ClassicalDedekindReals::DRealAbstr(_x0);
}

std::shared_ptr<CReal> RbaseSymbolsImpl::Rrepr(
    const DReal
        _x0) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return ClassicalDedekindReals::DRealRepr(_x0);
}

__attribute__((pure)) RbaseSymbolsImpl::R RbaseSymbolsImpl::Rplus(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &
        y) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return Rabst(ConstructiveCauchyReals::CReal_plus(Rrepr(x), Rrepr(y)));
}

__attribute__((pure)) RbaseSymbolsImpl::R RbaseSymbolsImpl::Rmult(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &
        y) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return Rabst(ConstructiveCauchyRealsMult::CReal_mult(Rrepr(x), Rrepr(y)));
}

__attribute__((pure)) RbaseSymbolsImpl::R RbaseSymbolsImpl::Ropp(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &
        x) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return Rabst(ConstructiveCauchyReals::CReal_opp(Rrepr(x)));
}

__attribute__((pure)) RbaseSymbolsImpl::R Rminus(const RbaseSymbolsImpl::R r1,
                                                 const RbaseSymbolsImpl::R r2) {
  return RbaseSymbolsImpl::Rplus(r1, RbaseSymbolsImpl::Ropp(r2));
}

__attribute__((pure)) RbaseSymbolsImpl::R
IPR_2(const std::shared_ptr<Positive> &p) {
  return std::visit(
      Overloaded{[](const typename Positive::XI _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::Rmult(
                       RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::R1,
                                               RbaseSymbolsImpl::R1),
                       RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::R1,
                                               IPR_2(_args.d_a0)));
                 },
                 [](const typename Positive::XO _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::Rmult(
                       RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::R1,
                                               RbaseSymbolsImpl::R1),
                       IPR_2(_args.d_a0));
                 },
                 [](const typename Positive::XH _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::R1,
                                                  RbaseSymbolsImpl::R1);
                 }},
      p->v());
}

__attribute__((pure)) RbaseSymbolsImpl::R
IPR(const std::shared_ptr<Positive> &p) {
  return std::visit(
      Overloaded{[](const typename Positive::XI _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::R1,
                                                  IPR_2(_args.d_a0));
                 },
                 [](const typename Positive::XO _args) -> RbaseSymbolsImpl::R {
                   return IPR_2(_args.d_a0);
                 },
                 [](const typename Positive::XH _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::R1;
                 }},
      p->v());
}

__attribute__((pure)) RbaseSymbolsImpl::R IZR(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::R0;
                 },
                 [](const typename Z::Zpos _args) -> RbaseSymbolsImpl::R {
                   return IPR(_args.d_a0);
                 },
                 [](const typename Z::Zneg _args) -> RbaseSymbolsImpl::R {
                   return RbaseSymbolsImpl::Ropp(IPR(_args.d_a0));
                 }},
      z->v());
}

std::shared_ptr<Sumor<bool>> total_order_T(const RbaseSymbolsImpl::R r1,
                                           const RbaseSymbolsImpl::R r2) {
  std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>> s =
      ConstructiveCauchyReals::CRealLt_lpo_dec(
          RbaseSymbolsImpl::Rrepr(r1), RbaseSymbolsImpl::Rrepr(r2),
          [](auto &&d_a0) -> decltype(auto) {
            return sig_forall_dec(std::forward<decltype(d_a0)>(d_a0));
          });
  return std::visit(
      Overloaded{
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::any>::Inl _args)
              -> std::shared_ptr<Sumor<bool>> {
            return Sumor<bool>::inleft(true);
          },
          [&](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::any>::Inr _args)
              -> std::shared_ptr<Sumor<bool>> {
            std::shared_ptr<
                Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>>
                s0 = ConstructiveCauchyReals::CRealLt_lpo_dec(
                    RbaseSymbolsImpl::Rrepr(r2), RbaseSymbolsImpl::Rrepr(r1),
                    [](auto &&d_a0) -> decltype(auto) {
                      return sig_forall_dec(std::forward<decltype(d_a0)>(d_a0));
                    });
            return std::visit(
                Overloaded{
                    [](const typename Sum<
                        std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::Inl
                           _args0) -> std::shared_ptr<Sumor<bool>> {
                      return Sumor<bool>::inright();
                    },
                    [](const typename Sum<
                        std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::Inr
                           _args0) -> std::shared_ptr<Sumor<bool>> {
                      return Sumor<bool>::inleft(false);
                    }},
                std::move(s0)->v());
          }},
      std::move(s)->v());
}

__attribute__((pure)) bool Req_appart_dec(const RbaseSymbolsImpl::R x,
                                          const RbaseSymbolsImpl::R y) {
  std::shared_ptr<Sumor<bool>> s = total_order_T(x, y);
  return std::visit(
      Overloaded{[](const typename Sumor<bool>::Inleft _args) -> bool {
                   if (_args.d_a0) {
                     return false;
                   } else {
                     return true;
                   }
                 },
                 [](const typename Sumor<bool>::Inright _args) -> bool {
                   return false;
                 }},
      std::move(s)->v());
}

__attribute__((pure)) CReal_appart Rrepr_appart_0(const RbaseSymbolsImpl::R x) {
  return ConstructiveRcomplete::CRealLtDisjunctEpsilon(
      RbaseSymbolsImpl::Rrepr(x),
      ConstructiveCauchyReals::inject_Q(
          std::make_shared<Q>(Q{Z::z0(), Positive::xh()})),
      ConstructiveCauchyReals::inject_Q(
          std::make_shared<Q>(Q{Z::z0(), Positive::xh()})),
      RbaseSymbolsImpl::Rrepr(x));
}

__attribute__((pure)) RbaseSymbolsImpl::R
RinvImpl::Rinv(const RbaseSymbolsImpl::R x) {
  if (::Req_appart_dec(x, RbaseSymbolsImpl::R0)) {
    return RbaseSymbolsImpl::R0;
  } else {
    return RbaseSymbolsImpl::Rabst(ConstructiveCauchyRealsMult::CReal_inv(
        RbaseSymbolsImpl::Rrepr(x), ::Rrepr_appart_0(x)));
  }
}

__attribute__((pure)) RbaseSymbolsImpl::R Rdiv(const RbaseSymbolsImpl::R r1,
                                               const RbaseSymbolsImpl::R r2) {
  return RbaseSymbolsImpl::Rmult(r1, RinvImpl::Rinv(r2));
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::sample_activation(const RbaseSymbolsImpl::R z) {
  return z;
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::sample_mu(const RbaseSymbolsImpl::R x) {
  return RinvImpl::Rinv(RbaseSymbolsImpl::Rplus(::IZR(Z::zpos(Positive::xh())),
                                                RbaseSymbolsImpl::Rmult(x, x)));
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::sample_gamma(const RbaseSymbolsImpl::R t) {
  return ::Rdiv(t, ::IZR(Z::zpos(Positive::xo(Positive::xh()))));
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::sample_v(const RbaseSymbolsImpl::R _x) {
  return RinvImpl::Rinv(
      ::IZR(Z::zpos(Positive::xo(Positive::xo(Positive::xh())))));
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::sample_N(const RbaseSymbolsImpl::R x) {
  return RbaseSymbolsImpl::Rplus(::IZR(Z::zpos(Positive::xh())),
                                 RbaseSymbolsImpl::Rmult(x, x));
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::density_radicand_at(const unsigned int n) {
  RbaseSymbolsImpl::R t = Raxioms::INR(n);
  return ::Rminus(
      Rpow_def::pow0(lapse(sample_activation, sample_mu, sample_gamma(t)), 2u),
      Rpow_def::pow0(sample_v(t), 2u));
}

__attribute__((pure)) bool
DensityPotentialTraceCase::static_time_nonnegative_at(const unsigned int n) {
  if (RIneq::Rle_dec(::IZR(Z::z0()),
                     proper_time_static(sample_activation, sample_mu,
                                        Raxioms::INR(n), sample_time))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
DensityPotentialTraceCase::density_radicand_nonnegative_at(
    const unsigned int n) {
  if (RIneq::Rle_dec(::IZR(Z::z0()), density_radicand_at(n))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) RbaseSymbolsImpl::R
DensityPotentialTraceCase::density_value_at(const unsigned int n) {
  return proper_time_density_path(sample_activation, sample_mu, sample_gamma,
                                  sample_v, Raxioms::INR(n));
}

__attribute__((pure)) bool
DensityPotentialTraceCase::density_value_nonnegative_at(const unsigned int n) {
  if (RIneq::Rle_dec(::IZR(Z::z0()), density_value_at(n))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
DensityPotentialTraceCase::massive_potential_nonnegative_at(
    const unsigned int n) {
  if (RIneq::Rle_dec(::IZR(Z::z0()),
                     V_eff_massive(sample_N, sample_mass, Raxioms::INR(n)))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) Comparison Datatypes::CompOpp(const Comparison r) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) arrow<std::any, std::any>
CMorphisms::iffT_arrow_subrelation(
    const std::pair<std::function<std::any(std::any)>,
                    std::function<std::any(std::any)>>
        x) {
  return [=](std::any x0) mutable {
    T1 a = x.first;
    T2 _x = x.second;
    return a(x0);
  };
}

__attribute__((pure)) arrow<std::any, std::any>
CMorphisms::iffT_flip_arrow_subrelation(
    const std::pair<std::function<std::any(std::any)>,
                    std::function<std::any(std::any)>>
        x) {
  return [=](std::any x0) mutable {
    T1 _x = x.first;
    T2 b = x.second;
    return b(x0);
  };
}

__attribute__((pure)) unsigned int
ConstructiveExtra::Z_inj_nat(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> unsigned int { return 0u; },
                 [](const typename Z::Zpos _args) -> unsigned int {
                   return Coq_Pos::to_nat(Positive::xo(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> unsigned int {
                   return Coq_Pos::to_nat(Coq_Pos::pred_double(_args.d_a0));
                 }},
      z->v());
}

std::shared_ptr<Z> ConstructiveExtra::Z_inj_nat_rev(const unsigned int n) {
  if (n <= 0) {
    return Z::z0();
  } else {
    unsigned int _x = n - 1;
    return std::visit(
        Overloaded{[](const typename Positive::XI _args) -> std::shared_ptr<Z> {
                     return Z::zneg(Coq_Pos::succ(_args.d_a0));
                   },
                   [](const typename Positive::XO _args) -> std::shared_ptr<Z> {
                     return Z::zpos(_args.d_a0);
                   },
                   [](const typename Positive::XH _args) -> std::shared_ptr<Z> {
                     return Z::zneg(Positive::xh());
                   }},
        Coq_Pos::of_nat(n)->v());
  }
}

std::shared_ptr<Q> QArith_base::Qplus(std::shared_ptr<Q> x,
                                      std::shared_ptr<Q> y) {
  return std::make_shared<Q>(
      Q{BinInt::add(BinInt::mul(x->Qnum, Z::zpos(y->Qden)),
                    BinInt::mul(y->Qnum, Z::zpos(x->Qden))),
        Coq_Pos::mul(x->Qden, y->Qden)});
}

std::shared_ptr<Q> QArith_base::Qmult(std::shared_ptr<Q> x,
                                      std::shared_ptr<Q> y) {
  return std::make_shared<Q>(
      Q{BinInt::mul(x->Qnum, y->Qnum), Coq_Pos::mul(x->Qden, y->Qden)});
}

std::shared_ptr<Q> QArith_base::Qopp(std::shared_ptr<Q> x) {
  return std::make_shared<Q>(Q{BinInt::opp(x->Qnum), x->Qden});
}

std::shared_ptr<Q> QArith_base::Qminus(const std::shared_ptr<Q> &x,
                                       const std::shared_ptr<Q> &y) {
  return QArith_base::Qplus(x, QArith_base::Qopp(y));
}

std::shared_ptr<Q> QArith_base::Qinv(std::shared_ptr<Q> x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Q> {
                   return std::make_shared<Q>(Q{Z::z0(), Positive::xh()});
                 },
                 [&](const typename Z::Zpos _args) -> std::shared_ptr<Q> {
                   return std::make_shared<Q>(
                       Q{Z::zpos(std::move(x)->Qden), _args.d_a0});
                 },
                 [&](const typename Z::Zneg _args) -> std::shared_ptr<Q> {
                   return std::make_shared<Q>(
                       Q{Z::zneg(std::move(x)->Qden), _args.d_a0});
                 }},
      x->Qnum->v());
}

std::shared_ptr<Q> QArith_base::Qdiv(const std::shared_ptr<Q> &x,
                                     const std::shared_ptr<Q> &y) {
  return QArith_base::Qmult(x, QArith_base::Qinv(y));
}

__attribute__((pure)) bool QArith_base::Qlt_le_dec(std::shared_ptr<Q> x,
                                                   std::shared_ptr<Q> y) {
  return BinInt::mul(x->Qnum, Z::zpos(y->Qden))
      ->Z_lt_le_dec(BinInt::mul(y->Qnum, Z::zpos(x->Qden)));
}

std::shared_ptr<Sig<std::shared_ptr<Positive>>>
QArith_base::Qarchimedean(const std::shared_ptr<Q> &q) {
  return [&](void) {
    std::shared_ptr<Z> qnum = q->Qnum;
    std::any _x = q->Qden;
    return std::visit(
        Overloaded{
            [](const typename Z::Z0 _args)
                -> std::shared_ptr<Sig<std::shared_ptr<Positive>>> {
              return Sig<std::shared_ptr<Positive>>::exist(Positive::xh());
            },
            [](const typename Z::Zpos _args)
                -> std::shared_ptr<Sig<std::shared_ptr<Positive>>> {
              return Sig<std::shared_ptr<Positive>>::exist(
                  Coq_Pos::add(_args.d_a0, Positive::xh()));
            },
            [](const typename Z::Zneg _args)
                -> std::shared_ptr<Sig<std::shared_ptr<Positive>>> {
              return Sig<std::shared_ptr<Positive>>::exist(Positive::xh());
            }},
        qnum->v());
  }();
}

std::shared_ptr<Q>
QArith_base::Qpower_positive(const std::shared_ptr<Q> &_x0,
                             const std::shared_ptr<Positive> &_x1) {
  return Ring_theory::template pow_pos<std::shared_ptr<Q>>(QArith_base::Qmult,
                                                           _x0, _x1);
}

std::shared_ptr<Q> QArith_base::Qpower(const std::shared_ptr<Q> &q,
                                       const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Q> {
                   return std::make_shared<Q>(
                       Q{Z::zpos(Positive::xh()), Positive::xh()});
                 },
                 [&](const typename Z::Zpos _args) -> std::shared_ptr<Q> {
                   return QArith_base::Qpower_positive(q, _args.d_a0);
                 },
                 [&](const typename Z::Zneg _args) -> std::shared_ptr<Q> {
                   return QArith_base::Qinv(
                       QArith_base::Qpower_positive(q, _args.d_a0));
                 }},
      z->v());
}

std::shared_ptr<Q> Qabs::Qabs(const std::shared_ptr<Q> &x) {
  return [&](void) {
    std::shared_ptr<Z> n = x->Qnum;
    std::shared_ptr<Positive> d = x->Qden;
    return std::make_shared<Q>(Q{BinInt::abs(n), d});
  }();
}

std::shared_ptr<Z> Qround::Qfloor(const std::shared_ptr<Q> &x) {
  return [&](void) {
    std::shared_ptr<Z> n = x->Qnum;
    std::shared_ptr<Positive> d = x->Qden;
    return BinInt::div(n, Z::zpos(d));
  }();
}

std::shared_ptr<Q> Qreduction::Qred(const std::shared_ptr<Q> &q) {
  return [&](void) {
    std::shared_ptr<Z> q1 = q->Qnum;
    std::shared_ptr<Positive> q2 = q->Qden;
    std::shared_ptr<Z> r1 = BinInt::ggcd(q1, Z::zpos(q2)).second.first;
    std::shared_ptr<Z> r2 = BinInt::ggcd(q1, Z::zpos(q2)).second.second;
    return std::make_shared<Q>(Q{r1, BinInt::to_pos(r2)});
  }();
}

std::shared_ptr<Positive>
QExtra::Pos_log2floor_plus1(const std::shared_ptr<Positive> &p) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Coq_Pos::succ(QExtra::Pos_log2floor_plus1(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Coq_Pos::succ(QExtra::Pos_log2floor_plus1(_args.d_a0));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::xh();
          }},
      p->v());
}

std::shared_ptr<Z> QExtra::Qbound_lt_ZExp2(const std::shared_ptr<Q> &q) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::zneg(Positive::xo(Positive::xo(Positive::xo(
                       Positive::xi(Positive::xo(Positive::xi(Positive::xi(
                           Positive::xi(Positive::xi(Positive::xh()))))))))));
                 },
                 [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return BinInt::pos_sub(
                       Coq_Pos::succ(QExtra::Pos_log2floor_plus1(_args.d_a0)),
                       QExtra::Pos_log2floor_plus1(q->Qden));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::z0();
                 }},
      q->Qnum->v());
}

std::shared_ptr<Z> QExtra::Qbound_ltabs_ZExp2(const std::shared_ptr<Q> &q) {
  return QExtra::Qbound_lt_ZExp2(Qabs::Qabs(q));
}

std::shared_ptr<Sig<std::shared_ptr<Z>>>
QExtra::QarchimedeanExp2_Z(std::shared_ptr<Q> q) {
  return Sig<std::shared_ptr<Z>>::exist(QExtra::Qbound_lt_ZExp2(std::move(q)));
}

std::shared_ptr<Sig<std::shared_ptr<Q>>>
ConstructiveLUB::DDcut_limit_fix(std::shared_ptr<DedekindDecCut> upcut,
                                 std::shared_ptr<Q> r, const unsigned int n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    bool s = upcut->DDdec(QArith_base::Qplus(
        upcut->DDlow,
        QArith_base::Qmult(
            std::make_shared<Q>(Q{BinInt::of_nat(n0), Positive::xh()}), r)));
    if (std::move(s)) {
      return ConstructiveLUB::DDcut_limit_fix(upcut, std::move(r), n0);
    } else {
      return Sig<std::shared_ptr<Q>>::exist(QArith_base::Qplus(
          upcut->DDlow,
          QArith_base::Qmult(
              std::make_shared<Q>(Q{BinInt::of_nat((n0 + 1)), Positive::xh()}),
              std::move(r))));
    }
  }
}

std::shared_ptr<Sig<std::shared_ptr<Q>>>
ConstructiveLUB::DDcut_limit(const std::shared_ptr<DedekindDecCut> &upcut,
                             const std::shared_ptr<Q> &r) {
  std::shared_ptr<Sig<std::shared_ptr<Positive>>> s = QArith_base::Qarchimedean(
      QArith_base::Qdiv(QArith_base::Qminus(upcut->DDhigh, upcut->DDlow), r));
  return std::visit(
      Overloaded{[&](const typename Sig<std::shared_ptr<Positive>>::Exist _args)
                     -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
        return ConstructiveLUB::DDcut_limit_fix(upcut, r,
                                                Coq_Pos::to_nat(_args.d_a0));
      }},
      std::move(s)->v());
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CRealLtEpsilon(std::shared_ptr<CReal> x,
                                        std::shared_ptr<CReal> y) {
  return ConstructiveExtra::constructive_indefinite_ground_description_Z(
      [=](std::shared_ptr<Z> n) mutable {
        bool hdec = QArith_base::Qlt_le_dec(
            QArith_base::Qmult(
                std::make_shared<Q>(
                    Q{Z::zpos(Positive::xo(Positive::xh())), Positive::xh()}),
                QArith_base::Qpower(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    n)),
            QArith_base::Qminus(y->seq(n), x->seq(n)));
        if (std::move(hdec)) {
          return true;
        } else {
          return false;
        }
      });
}

std::shared_ptr<Sig<std::shared_ptr<Z>>> ConstructiveCauchyReals::CRealLt_above(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &h) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq y n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{[&](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
        std::shared_ptr<Sig<std::shared_ptr<Z>>> s =
            QExtra::QarchimedeanExp2_Z(QArith_base::Qinv(QArith_base::Qminus(
                QArith_base::Qminus(y->seq(_args.d_a0), x->seq(_args.d_a0)),
                QArith_base::Qmult(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    QArith_base::Qpower(
                        std::make_shared<Q>(
                            Q{Z::zpos(Positive::xo(Positive::xh())),
                              Positive::xh()}),
                        _args.d_a0)))));
        return [&](void) {
          if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
            auto &_rf = std::get<0>(std::move(s)->v_mut());
            std::shared_ptr<Z> x1 = std::move(_rf.d_a0);
            _rf.d_a0 = BinInt::min(BinInt::sub(BinInt::opp(std::move(x1)),
                                               Z::zpos(Positive::xh())),
                                   _args.d_a0);
            return std::move(s);
          } else {
            return std::visit(
                Overloaded{
                    [&](const typename Sig<std::shared_ptr<Z>>::Exist _args0)
                        -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
                      return Sig<std::shared_ptr<Z>>::exist(
                          BinInt::min(BinInt::sub(BinInt::opp(_args0.d_a0),
                                                  Z::zpos(Positive::xh())),
                                      _args.d_a0));
                    }},
                std::move(s)->v());
          }
        }();
      }},
      h->v());
}

std::shared_ptr<
    Sum<ConstructiveCauchyReals::CRealLt, ConstructiveCauchyReals::CRealLt>>
ConstructiveCauchyReals::CRealLt_dec(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &h) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq y n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{[&](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> std::shared_ptr<
                         Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                             std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
        std::shared_ptr<Sig<std::shared_ptr<Z>>> s =
            QExtra::QarchimedeanExp2_Z(QArith_base::Qinv(QArith_base::Qminus(
                QArith_base::Qminus(y->seq(_args.d_a0), x->seq(_args.d_a0)),
                QArith_base::Qmult(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    QArith_base::Qpower(
                        std::make_shared<Q>(
                            Q{Z::zpos(Positive::xo(Positive::xh())),
                              Positive::xh()}),
                        _args.d_a0)))));
        return std::visit(
            Overloaded{[&](const typename Sig<std::shared_ptr<Z>>::Exist _args0)
                           -> std::shared_ptr<
                               Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                   std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
              bool s0 = QArith_base::Qlt_le_dec(
                  QArith_base::Qmult(
                      std::make_shared<Q>(Q{Z::zpos(Positive::xh()),
                                            Positive::xo(Positive::xh())}),
                      QArith_base::Qplus(y->seq(_args.d_a0),
                                         x->seq(_args.d_a0))),
                  z->seq(BinInt::min(
                      _args.d_a0,
                      BinInt::sub(BinInt::opp(_args0.d_a0),
                                  Z::zpos(Positive::xo(Positive::xh()))))));
              if (std::move(s0)) {
                return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                           std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                    inl(Sig<std::shared_ptr<Z>>::exist(BinInt::min(
                        _args.d_a0,
                        BinInt::sub(BinInt::opp(_args0.d_a0),
                                    Z::zpos(Positive::xo(Positive::xh()))))));
              } else {
                return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                           std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                    inr(Sig<std::shared_ptr<Z>>::exist(BinInt::min(
                        _args.d_a0,
                        BinInt::sub(BinInt::opp(_args0.d_a0),
                                    Z::zpos(Positive::xo(Positive::xh()))))));
              }
            }},
            std::move(s)->v());
      }},
      h->v());
}

std::shared_ptr<
    Sum<ConstructiveCauchyReals::CRealLt, ConstructiveCauchyReals::CRealLt>>
ConstructiveCauchyReals::linear_order_T(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const ConstructiveCauchyReals::CRealLt
        _x0) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq z n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq z n)(
              ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return ConstructiveCauchyReals::CRealLt_dec(x, z, y, _x0);
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_le_lt_trans(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &hlt) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq z n)(ConstructiveCauchyReals.seq y n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq z n)(
              ConstructiveCauchyReals.seq y n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                      std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
      s = ConstructiveCauchyReals::linear_order_T(y, x, z, hlt);
  return std::visit(
      Overloaded{
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            throw std::logic_error("absurd case");
          },
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            return _args.d_a0;
          }},
      std::move(s)->v());
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_lt_le_trans(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &hlt) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq y n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                      std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
      s = ConstructiveCauchyReals::linear_order_T(x, z, y, hlt);
  return std::visit(
      Overloaded{
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            return _args.d_a0;
          },
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            throw std::logic_error("absurd case");
          }},
      std::move(s)->v());
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_lt_trans(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>> &hxlty,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &_x) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq z n)(ConstructiveCauchyReals.seq y n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq z n)(
              ConstructiveCauchyReals.seq y n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq y n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return ConstructiveCauchyReals::CReal_lt_le_trans(x, y, z, hxlty);
}

__attribute__((pure)) iffT<std::any, std::any>
ConstructiveCauchyReals::CRealLt_morph(std::shared_ptr<CReal> x,
                                       std::shared_ptr<CReal> y,
                                       std::shared_ptr<CReal> x0,
                                       std::shared_ptr<CReal> y0) {
  return std::make_pair(
      [=](std::any hxltx0) mutable {
        std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                            std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
            s = ConstructiveCauchyReals::CRealLt_dec(x, x0, y, hxltx0);
        return std::visit(
            Overloaded{
                [](const typename Sum<
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl _args)
                    -> std::any { throw std::logic_error("absurd case"); },
                [&](const typename Sum<
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr _args)
                    -> std::any {
                  std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                      std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
                      s0 = ConstructiveCauchyReals::CRealLt_dec(y, x0, y0,
                                                                _args.d_a0);
                  return std::visit(
                      Overloaded{
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                                 _args0) -> std::any { return _args0.d_a0; },
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                                 _args0) -> std::any {
                            throw std::logic_error("absurd case");
                          }},
                      std::move(s0)->v());
                }},
            std::move(s)->v());
      },
      [=](std::any hylty0) mutable {
        std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                            std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
            s = ConstructiveCauchyReals::CRealLt_dec(y, y0, x, hylty0);
        return std::visit(
            Overloaded{
                [](const typename Sum<
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl _args)
                    -> std::any { throw std::logic_error("absurd case"); },
                [&](const typename Sum<
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                    std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr _args)
                    -> std::any {
                  std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                      std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
                      s0 = ConstructiveCauchyReals::CRealLt_dec(x, y0, x0,
                                                                _args.d_a0);
                  return std::visit(
                      Overloaded{
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                                 _args0) -> std::any { return _args0.d_a0; },
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                                 _args0) -> std::any {
                            throw std::logic_error("absurd case");
                          }},
                      std::move(s0)->v());
                }},
            std::move(s)->v());
      });
}

std::shared_ptr<CReal> ConstructiveCauchyReals::inject_Q(std::shared_ptr<Q> q) {
  return std::make_shared<CReal>(
      CReal{[=](std::shared_ptr<Z> _x) mutable { return q; },
            QExtra::Qbound_ltabs_ZExp2(q)});
}

std::shared_ptr<Q>
ConstructiveCauchyReals::CReal_plus_seq(const std::shared_ptr<CReal> &x,
                                        const std::shared_ptr<CReal> &y,
                                        const std::shared_ptr<Z> &n) {
  return Qreduction::Qred(
      QArith_base::Qplus(x->seq(BinInt::sub(n, Z::zpos(Positive::xh()))),
                         y->seq(BinInt::sub(n, Z::zpos(Positive::xh())))));
}

std::shared_ptr<Z>
ConstructiveCauchyReals::CReal_plus_scale(const std::shared_ptr<CReal> &x,
                                          const std::shared_ptr<CReal> &y) {
  return BinInt::add(BinInt::max(x->scale, y->scale), Z::zpos(Positive::xh()));
}

std::shared_ptr<CReal>
ConstructiveCauchyReals::CReal_plus(std::shared_ptr<CReal> x,
                                    std::shared_ptr<CReal> y) {
  return std::make_shared<CReal>(
      CReal{[&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
              return ConstructiveCauchyReals::CReal_plus_seq(x, y, _x0);
            },
            ConstructiveCauchyReals::CReal_plus_scale(x, y)});
}

std::shared_ptr<Q>
ConstructiveCauchyReals::CReal_opp_seq(const std::shared_ptr<CReal> &x,
                                       const std::shared_ptr<Z> &n) {
  return QArith_base::Qopp(x->seq(n));
}

std::shared_ptr<Z>
ConstructiveCauchyReals::CReal_opp_scale(const std::shared_ptr<CReal> &x) {
  return x->scale;
}

std::shared_ptr<CReal>
ConstructiveCauchyReals::CReal_opp(std::shared_ptr<CReal> x) {
  return std::make_shared<CReal>(
      CReal{[&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
              return ConstructiveCauchyReals::CReal_opp_seq(x, _x0);
            },
            ConstructiveCauchyReals::CReal_opp_scale(x)});
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_plus_lt_compat_l(
    const std::shared_ptr<CReal> &_x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &hlt) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq z n)(ConstructiveCauchyReals.seq y n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq z n)(
              ConstructiveCauchyReals.seq y n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  std::shared_ptr<Sig<std::shared_ptr<Z>>> hlt0 =
      ConstructiveCauchyReals::CRealLt_above(y, z, hlt);
  return [&](void) {
    if (std::move(hlt0).use_count() == 1 && std::move(hlt0)->v().index() == 0) {
      auto &_rf = std::get<0>(std::move(hlt0)->v_mut());
      std::shared_ptr<Z> x = std::move(_rf.d_a0);
      _rf.d_a0 = std::move(x);
      return std::move(hlt0);
    } else {
      return std::visit(
          Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                         -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            return Sig<std::shared_ptr<Z>>::exist(_args.d_a0);
          }},
          std::move(hlt0)->v());
    }
  }();
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_plus_lt_reg_l(
    const std::shared_ptr<CReal> &_x, const std::shared_ptr<CReal> &_x0,
    const std::shared_ptr<CReal> &_x1,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &hlt) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq(
          ConstructiveCauchyReals.CReal_plus x z) n)(
          ConstructiveCauchyReals.seq(ConstructiveCauchyReals.CReal_plus x y)
              n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq(
              ConstructiveCauchyReals.CReal_plus x z) n)(
              ConstructiveCauchyReals.seq(
                  ConstructiveCauchyReals.CReal_plus x y) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
        return Sig<std::shared_ptr<Z>>::exist(
            BinInt::sub(_args.d_a0, Z::zpos(Positive::xh())));
      }},
      hlt->v());
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::CReal_plus_lt_reg_r(
    const std::shared_ptr<CReal> &x, const std::shared_ptr<CReal> &y,
    const std::shared_ptr<CReal> &z,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &hlt) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq(
          ConstructiveCauchyReals.CReal_plus z x) n)(
          ConstructiveCauchyReals.seq(ConstructiveCauchyReals.CReal_plus y x)
              n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq(
              ConstructiveCauchyReals.CReal_plus z x) n)(
              ConstructiveCauchyReals.seq(
                  ConstructiveCauchyReals.CReal_plus y x) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  std::any hlt0 = CMorphisms::subrelation_proper(
      ([]() -> std::any {
        throw std::logic_error("unreachable");
        return std::any{};
      })(),
      [](std::shared_ptr<CReal> x0, std::shared_ptr<CReal> x1,
         std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
        return ConstructiveCauchyReals::CRealLt_morph()(x0, x1, x2, x3);
      },
      Unit::e_TT,
      CMorphisms::subrelation_respectful(
          ([]() -> std::any {
            throw std::logic_error("unreachable");
            return std::any{};
          })(),
          CMorphisms::subrelation_respectful(
              ([]() -> std::any {
                throw std::logic_error("unreachable");
                return std::any{};
              })(),
              CMorphisms::iffT_arrow_subrelation)),
      ConstructiveCauchyReals::CReal_plus(y, x))(
      ConstructiveCauchyReals::CReal_plus(x, y),
      ConstructiveCauchyReals::CReal_plus(z, x),
      ConstructiveCauchyReals::CReal_plus(z, x), hlt);
  std::any hlt1 = CMorphisms::Reflexive_partial_app_morphism(
      ([]() -> std::any {
        throw std::logic_error("unreachable");
        return std::any{};
      })(),
      CMorphisms::subrelation_proper(
          ([]() -> std::any {
            throw std::logic_error("unreachable");
            return std::any{};
          })(),
          [](std::shared_ptr<CReal> x0, std::shared_ptr<CReal> x1,
             std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
            return ConstructiveCauchyReals::CRealLt_morph()(x0, x1, x2, x3);
          },
          Unit::e_TT,
          CMorphisms::subrelation_respectful(
              ([]() -> std::any {
                throw std::logic_error("unreachable");
                return std::any{};
              })(),
              CMorphisms::subrelation_respectful(
                  ([]() -> std::any {
                    throw std::logic_error("unreachable");
                    return std::any{};
                  })(),
                  CMorphisms::iffT_arrow_subrelation))),
      ConstructiveCauchyReals::CReal_plus(x, y))(
      ConstructiveCauchyReals::CReal_plus(z, x),
      ConstructiveCauchyReals::CReal_plus(x, z), hlt0);
  return ConstructiveCauchyReals::CReal_plus_lt_reg_l(x, y, z, hlt1);
}

__attribute__((pure)) ConstructiveCauchyReals::CRealLt
ConstructiveCauchyReals::inject_Q_lt(const std::shared_ptr<Q> &q,
                                     const std::shared_ptr<Q> &r) {
  std::shared_ptr<Sig<std::shared_ptr<Z>>> s =
      QExtra::QarchimedeanExp2_Z(QArith_base::Qinv(QArith_base::Qminus(r, q)));
  return [&](void) {
    if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
      auto &_rf = std::get<0>(std::move(s)->v_mut());
      std::shared_ptr<Z> x = std::move(_rf.d_a0);
      _rf.d_a0 =
          BinInt::sub(BinInt::opp(std::move(x)), Z::zpos(Positive::xh()));
      return std::move(s);
    } else {
      return std::visit(
          Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                         -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            return Sig<std::shared_ptr<Z>>::exist(
                BinInt::sub(BinInt::opp(_args.d_a0), Z::zpos(Positive::xh())));
          }},
          std::move(s)->v());
    }
  }();
}

std::shared_ptr<Q>
ConstructiveCauchyAbs::CReal_abs_seq(const std::shared_ptr<CReal> &x,
                                     const std::shared_ptr<Z> &n) {
  return Qabs::Qabs(x->seq(n));
}

std::shared_ptr<Z>
ConstructiveCauchyAbs::CReal_abs_scale(const std::shared_ptr<CReal> &x) {
  return x->scale;
}

std::shared_ptr<CReal>
ConstructiveCauchyAbs::CReal_abs(std::shared_ptr<CReal> x) {
  return std::make_shared<CReal>(
      CReal{[&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
              return ConstructiveCauchyAbs::CReal_abs_seq(x, _x0);
            },
            ConstructiveCauchyAbs::CReal_abs_scale(x)});
}

bool ClassicalDedekindReals::sig_not_dec() {
  throw std::logic_error(
      "unrealized axiom: Stdlib.Reals.ClassicalDedekindReals.sig_not_dec");
}

__attribute__((pure)) ClassicalDedekindReals::DReal
ClassicalDedekindReals::DRealAbstr(std::shared_ptr<CReal> x) {
  std::function<bool(std::shared_ptr<Q>, unsigned int)> h =
      [=](std::shared_ptr<Q> q, unsigned int n) mutable {
        bool s = QArith_base::Qlt_le_dec(
            QArith_base::Qplus(q, QArith_base::Qpower(
                                      std::make_shared<Q>(Q{
                                          Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                                      BinInt::opp(BinInt::of_nat(n)))),
            x->seq(BinInt::opp(BinInt::of_nat(n))));
        if (std::move(s)) {
          return false;
        } else {
          return true;
        }
      };
  return Sig<std::function<bool(
      std::shared_ptr<Q>)>>::exist([=](std::shared_ptr<Q> q) mutable {
    return std::visit(
        Overloaded{
            [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inleft
                   _args) -> bool { return true; },
            [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inright
                   _args) -> bool { return false; }},
        ClassicalDedekindReals::sig_forall_dec(h(q))->v());
  });
}

std::shared_ptr<Sig<std::shared_ptr<Q>>> ClassicalDedekindReals::DRealQlim(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
    const unsigned int
        n) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return std::visit(
      Overloaded{[&](const typename Sig<
                     std::function<bool(std::shared_ptr<Q>)>>::Exist _args)
                     -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
        std::shared_ptr<Sig<std::shared_ptr<Q>>> s =
            ClassicalDedekindReals::lowerCutAbove(_args.d_a0);
        return std::visit(
            Overloaded{[&](const typename Sig<std::shared_ptr<Q>>::Exist _args0)
                           -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
              std::shared_ptr<Sig<std::shared_ptr<Positive>>> s0 =
                  QArith_base::Qarchimedean(QArith_base::Qminus(
                      _args0.d_a0,
                      std::visit(
                          Overloaded{
                              [](const typename Sig<std::shared_ptr<Q>>::Exist
                                     _args1) -> auto { return _args1.d_a0; }},
                          ClassicalDedekindReals::lowerCutBelow(_args.d_a0)
                              ->v())));
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<std::shared_ptr<Positive>>::Exist
                              _args2)
                          -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                        return ClassicalDedekindReals::DRealQlim_rec(
                            _args.d_a0, n,
                            ((n + 1) * Coq_Pos::to_nat(_args2.d_a0)));
                      }},
                  std::move(s0)->v());
            }},
            std::move(s)->v());
      }},
      x->v());
}

std::shared_ptr<Sig<std::shared_ptr<Q>>> ClassicalDedekindReals::DRealQlimExp2(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
    const unsigned int
        n) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  std::shared_ptr<Sig<std::shared_ptr<Q>>> s =
      ClassicalDedekindReals::DRealQlim(x, (PeanoNat::pow(2u, n)
                                                ? PeanoNat::pow(2u, n) - 1
                                                : PeanoNat::pow(2u, n)));
  return [&](void) {
    if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
      auto &_rf = std::get<0>(std::move(s)->v_mut());
      std::shared_ptr<Q> x0 = std::move(_rf.d_a0);
      _rf.d_a0 = std::move(x0);
      return std::move(s);
    } else {
      return std::visit(
          Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist _args)
                         -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
            return Sig<std::shared_ptr<Q>>::exist(_args.d_a0);
          }},
          std::move(s)->v());
    }
  }();
}

std::shared_ptr<Q> ClassicalDedekindReals::CReal_of_DReal_seq(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
    const std::shared_ptr<Z> &
        n) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return std::visit(
      Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist _args)
                     -> auto { return _args.d_a0; }},
      ClassicalDedekindReals::DRealQlimExp2(x, BinInt::to_nat(BinInt::opp(n)))
          ->v());
}

std::shared_ptr<Z> ClassicalDedekindReals::CReal_of_DReal_scale(
    const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &
        x) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return QExtra::Qbound_lt_ZExp2(QArith_base::Qplus(
      Qabs::Qabs(ClassicalDedekindReals::CReal_of_DReal_seq(
          x, Z::zneg(Positive::xh()))),
      std::make_shared<Q>(
          Q{Z::zpos(Positive::xo(Positive::xh())), Positive::xh()})));
}

std::shared_ptr<CReal> ClassicalDedekindReals::DRealRepr(
    std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>>
        x) { // Precondition: ((forall q r : QArith_base.Q, QArith_base.Qle q r -> f r = true -> f q = true) /\
 ~ (forall q : QArith_base.Q, f q = true) /\
 ~ (forall q : QArith_base.Q, f q = false) /\
 (forall q : QArith_base.Q,
  f q = true ->
  ~ (forall r : QArith_base.Q, QArith_base.Qle r q \/ f r = false)))
assert(true);
  return std::make_shared<CReal>(
      CReal{[&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
              return ClassicalDedekindReals::CReal_of_DReal_seq(x, _x0);
            },
            ClassicalDedekindReals::CReal_of_DReal_scale(x)});
}

std::shared_ptr<Q>
ConstructiveCauchyRealsMult::CReal_mult_seq(const std::shared_ptr<CReal> &x,
                                            const std::shared_ptr<CReal> &y,
                                            const std::shared_ptr<Z> &n) {
  return QArith_base::Qmult(
      x->seq(BinInt::sub(BinInt::sub(n, y->scale), Z::zpos(Positive::xh()))),
      y->seq(BinInt::sub(BinInt::sub(n, x->scale), Z::zpos(Positive::xh()))));
}

std::shared_ptr<Z>
ConstructiveCauchyRealsMult::CReal_mult_scale(const std::shared_ptr<CReal> &x,
                                              const std::shared_ptr<CReal> &y) {
  return BinInt::add(x->scale, y->scale);
}

std::shared_ptr<CReal>
ConstructiveCauchyRealsMult::CReal_mult(std::shared_ptr<CReal> x,
                                        std::shared_ptr<CReal> y) {
  return std::make_shared<CReal>(
      CReal{[&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
              return ConstructiveCauchyRealsMult::CReal_mult_seq(x, y, _x0);
            },
            ConstructiveCauchyRealsMult::CReal_mult_scale(x, y)});
}

__attribute__((pure)) CRealLt
ConstructiveCauchyRealsMult::CReal_mult_lt_0_compat(
    const std::shared_ptr<CReal> &_x, const std::shared_ptr<CReal> &_x0,
    std::shared_ptr<Sig<std::shared_ptr<Z>>> hx,
    std::shared_ptr<Sig<std::shared_ptr<Z>>>
        hy) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq y n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return Sig<std::shared_ptr<Z>>::exist(BinInt::sub(
      BinInt::add(
          std::visit(Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist
                                       _args) -> auto { return _args.d_a0; }},
                     std::move(hx)->v()),
          std::visit(Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist
                                       _args0) -> auto { return _args0.d_a0; }},
                     std::move(hy)->v())),
      Z::zpos(Positive::xh())));
}

std::shared_ptr<SigT<std::shared_ptr<Z>, std::pair<CRealLt, CRealLt>>>
ConstructiveCauchyRealsMult::CRealArchimedean(const std::shared_ptr<CReal> &x) {
  std::shared_ptr<Q> q = QArith_base::Qplus(
      x->seq(Z::zneg(Positive::xi(Positive::xh()))),
      std::make_shared<Q>(Q{Z::zpos(Positive::xi(Positive::xh())),
                            Positive::xo(Positive::xh())}));
  return SigT<std::shared_ptr<Z>,
              std::pair<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                        std::shared_ptr<Sig<std::shared_ptr<Z>>>>>::
      existt(Qround::Qfloor(std::move(q)),
             std::make_pair(Sig<std::shared_ptr<Z>>::exist(
                                Z::zneg(Positive::xi(Positive::xh()))),
                            Sig<std::shared_ptr<Z>>::exist(
                                Z::zneg(Positive::xi(Positive::xh())))));
}

std::shared_ptr<Z> ConstructiveCauchyRealsMult::CRealLowerBound(
    const std::shared_ptr<CReal> &_x,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &xPos) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> auto { return _args.d_a0; }},
      xPos->v());
}

std::shared_ptr<Z> ConstructiveCauchyRealsMult::CReal_inv_pos_cm(
    const std::shared_ptr<CReal> &x,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos,
    const std::shared_ptr<Z> &n) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return BinInt::min(
      ConstructiveCauchyRealsMult::CRealLowerBound(x, xPos),
      BinInt::add(n, BinInt::mul(Z::zpos(Positive::xo(Positive::xh())),
                                 ConstructiveCauchyRealsMult::CRealLowerBound(
                                     x, xPos))));
}

std::shared_ptr<Q> ConstructiveCauchyRealsMult::CReal_inv_pos_seq(
    const std::shared_ptr<CReal> &x,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos,
    const std::shared_ptr<Z> &n) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return QArith_base::Qinv(
      x->seq(ConstructiveCauchyRealsMult::CReal_inv_pos_cm(x, xPos, n)));
}

std::shared_ptr<Z> ConstructiveCauchyRealsMult::CReal_inv_pos_scale(
    const std::shared_ptr<CReal> &x,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &xPos) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return BinInt::opp(ConstructiveCauchyRealsMult::CRealLowerBound(x, xPos));
}

std::shared_ptr<CReal> ConstructiveCauchyRealsMult::CReal_inv_pos(
    std::shared_ptr<CReal> x,
    std::shared_ptr<Sig<std::shared_ptr<Z>>>
        hxpos) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq x n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::make_shared<CReal>(CReal{
      [&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
        return ConstructiveCauchyRealsMult::CReal_inv_pos_seq(x, hxpos, _x0);
      },
      ConstructiveCauchyRealsMult::CReal_inv_pos_scale(x, hxpos)});
}

__attribute__((pure)) CRealLt ConstructiveCauchyRealsMult::CReal_neg_lt_pos(
    const std::shared_ptr<CReal> &_x,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &h) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
            | QArith_base.Qnum : = 0;
            QArith_base.Qden : = 1 |
          }) n)(ConstructiveCauchyReals.seq x n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)(ConstructiveCauchyReals.seq x n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{[](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
        return Sig<std::shared_ptr<Z>>::exist(_args.d_a0);
      }},
      h->v());
}

std::shared_ptr<CReal> ConstructiveCauchyRealsMult::CReal_inv(
    const std::shared_ptr<CReal> &x,
    const std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>> &xnz) {
  return std::visit(
      Overloaded{
          [&](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                  _args) -> std::shared_ptr<CReal> {
            return ConstructiveCauchyReals::CReal_opp(
                ConstructiveCauchyRealsMult::CReal_inv_pos(
                    ConstructiveCauchyReals::CReal_opp(x),
                    ConstructiveCauchyRealsMult::CReal_neg_lt_pos(x,
                                                                  _args.d_a0)));
          },
          [&](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                  _args) -> std::shared_ptr<CReal> {
            return ConstructiveCauchyRealsMult::CReal_inv_pos(x, _args.d_a0);
          }},
      xnz->v());
}

__attribute__((pure)) CRealLt
ConstructiveCauchyRealsMult::CReal_inv_0_lt_compat(
    std::shared_ptr<CReal> r,
    const std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>> &hrnz,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &_x) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(
          QArith_base.Qden(QArith_base.Qminus(ConstructiveCauchyReals.seq r n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq r n)(
              ConstructiveCauchyReals.seq(ConstructiveCauchyReals.inject_Q {
                | QArith_base.Qnum : = 0;
                QArith_base.Qden : = 1 |
              }) n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::visit(
      Overloaded{
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            throw std::logic_error("absurd case");
          },
          [&](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                  _args) -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
            return Sig<std::shared_ptr<Z>>::exist(BinInt::sub(
                BinInt::opp(std::move(r)->scale), Z::zpos(Positive::xh())));
          }},
      hrnz->v());
}

std::shared_ptr<SigT<std::shared_ptr<Q>, std::pair<CRealLt, CRealLt>>>
ConstructiveCauchyRealsMult::CRealQ_dense(
    std::shared_ptr<CReal> a, std::shared_ptr<CReal> b,
    const std::shared_ptr<Sig<std::shared_ptr<Z>>>
        &h) { // Precondition: (QArith_base.Qnum
  (QArith_base.Qmult {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  }(QArith_base.Qpower {
    | QArith_base.Qnum : = 2;
    QArith_base.Qden : = 1 |
  } n)) *
      Z.pos(QArith_base.Qden(QArith_base.Qminus(
          ConstructiveCauchyReals.seq b n)(ConstructiveCauchyReals.seq a n)))
      ? = QArith_base.Qnum(QArith_base.Qminus(ConstructiveCauchyReals.seq b n)(
              ConstructiveCauchyReals.seq a n)) *
              Z.pos(QArith_base.Qden(QArith_base.Qmult {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              }(QArith_base.Qpower {
                | QArith_base.Qnum : = 2;
                QArith_base.Qden : = 1 |
              } n)))) %
          Z ==
        Lt assert(true);
  return std::
      visit(
          Overloaded{
              [&](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                  -> std::
                      shared_ptr<
                          SigT<std::shared_ptr<Q>,
                               std::pair<
                                   std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                   std::shared_ptr<Sig<std::shared_ptr<Z>>>>>> {
                        return SigT<
                            std::shared_ptr<Q>,
                            std::pair<
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>>::
                            existt(
                                QArith_base::Qmult(
                                    QArith_base::Qplus(a->seq(_args.d_a0),
                                                       b->seq(_args.d_a0)),
                                    std::make_shared<Q>(
                                        Q{Z::zpos(Positive::xh()),
                                          Positive::xo(Positive::xh())})),
                                std::make_pair(
                                    ConstructiveCauchyReals::CReal_le_lt_trans(
                                        a,
                                        ConstructiveCauchyReals::inject_Q(
                                            QArith_base::Qplus(
                                                a->seq(_args.d_a0),
                                                QArith_base::Qpower(
                                                    std::make_shared<Q>(
                                                        Q{Z::zpos(Positive::xo(
                                                              Positive::xh())),
                                                          Positive::xh()}),
                                                    _args.d_a0))),
                                        ConstructiveCauchyReals::inject_Q(
                                            QArith_base::Qmult(
                                                QArith_base::Qplus(
                                                    a->seq(_args.d_a0),
                                                    b->seq(_args.d_a0)),
                                                std::make_shared<Q>(
                                                    Q{Z::zpos(Positive::xh()),
                                                      Positive::xo(
                                                          Positive::xh())}))),
                                        ConstructiveCauchyReals::inject_Q_lt(
                                            QArith_base::Qplus(
                                                a->seq(_args.d_a0),
                                                QArith_base::Qpower(
                                                    std::make_shared<Q>(
                                                        Q{Z::zpos(Positive::xo(
                                                              Positive::xh())),
                                                          Positive::xh()}),
                                                    _args.d_a0)),
                                            QArith_base::Qmult(
                                                QArith_base::Qplus(
                                                    a->seq(_args.d_a0),
                                                    b->seq(_args.d_a0)),
                                                std::make_shared<Q>(
                                                    Q{Z::zpos(Positive::xh()),
                                                      Positive::xo(
                                                          Positive::xh())})))),
                                    ConstructiveCauchyReals::
                                        CReal_plus_lt_reg_l(ConstructiveCauchyReals::
                                                                CReal_opp(b),
                                                            ConstructiveCauchyReals::
                                                                inject_Q(
                                                                    QArith_base::
                                                                        Qmult(QArith_base::Qplus(a->seq(_args
                                                                                                            .d_a0),
                                                                                                 b->seq(_args
                                                                                                            .d_a0)),
                                                                              std::make_shared<
                                                                                  Q>(Q{Z::zpos(Positive::xh()), Positive::
                                                                                                                    xo(Positive::xh())}))),
                                                            b,
                                                            CMorphisms::Reflexive_partial_app_morphism(([]()
                                                                                                            -> std::any {
                                                                                                         throw std::
                                                                                                             logic_error(
                                                                                                                 "unreachable");
                                                                                                         return std::
                                                                                                             any{};
                                                                                                       })(),
                                                                                                       CMorphisms::subrelation_proper(([]() -> std::
                                                                                                                                                any {
                                                                                                                                                  throw std::
                                                                                                                                                      logic_error(
                                                                                                                                                          "unreachable");
                                                                                                                                                  return std::
                                                                                                                                                      any{};
                                                                                                                                                })(),
                                                                                                                                      [](
                                                                                                                                          std::shared_ptr<
                                                                                                                                              CReal>
                                                                                                                                              x0,
                                                                                                                                          std::shared_ptr<
                                                                                                                                              CReal>
                                                                                                                                              x1,
                                                                                                                                          std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
                                                                                                                                        return ConstructiveCauchyReals::
                                                                                                                                            CRealLt_morph()(
                                                                                                                                                x0,
                                                                                                                                                x1,
                                                                                                                                                x2,
                                                                                                                                                x3);
                                                                                                                                      },
                                                                                                                                      Unit::
                                                                                                                                          e_TT,
                                                                                                                                      CMorphisms::subrelation_respectful(
                                                                                                                                          ([]()
                                                                                                                                               -> std::any {
                                                                                                                                            throw std::
                                                                                                                                                logic_error(
                                                                                                                                                    "unreachable");
                                                                                                                                            return std::
                                                                                                                                                any{};
                                                                                                                                          })(),
                                                                                                                                          CMorphisms::subrelation_respectful(
                                                                                                                                              ([]() -> std::
                                                                                                                                                        any {
                                                                                                                                                          throw std::
                                                                                                                                                              logic_error(
                                                                                                                                                                  "unreachable");
                                                                                                                                                          return std::
                                                                                                                                                              any{};
                                                                                                                                                        })(),
                                                                                                                                              CMorphisms::
                                                                                                                                                  iffT_flip_arrow_subrelation))),
                                                                                                       ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::CReal_opp(b), ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                        Qmult(QArith_base::
                                                                                                                                                                                                                                  Qplus(a->seq(_args
                                                                                                                                                                                                                                                   .d_a0),
                                                                                                                                                                                                                                        b->seq(_args
                                                                                                                                                                                                                                                   .d_a0)),
                                                                                                                                                                                                                              std::make_shared<
                                                                                                                                                                                                                                  Q>(Q{
                                                                                                                                                                                                                                  Z::zpos(Positive::xh()), Positive::xo(Positive::xh())})))))(ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::CReal_opp(b), b), ConstructiveCauchyReals::inject_Q(std::make_shared<Q>(Q{Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                              ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                  CReal_plus_lt_reg_r(
                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::CReal_opp(ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                          QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                              QArith_base::
                                                                                                                                                                                                                                                                                                                  Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                            _args
                                                                                                                                                                                                                                                                                                                                .d_a0),
                                                                                                                                                                                                                                                                                                                        b->seq(
                                                                                                                                                                                                                                                                                                                            _args
                                                                                                                                                                                                                                                                                                                                .d_a0)),
                                                                                                                                                                                                                                                                                                              std::
                                                                                                                                                                                                                                                                                                                  make_shared<Q>(Q{Z::zpos(Positive::xh()), Positive::
                                                                                                                                                                                                                                                                                                                                                                xo(Positive::xh())})))),
                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                          CReal_plus(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                         CReal_opp(
                                                                                                                                                                                                                                                                                                                             b),
                                                                                                                                                                                                                                                                                                                     ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                         QArith_base::
                                                                                                                                                                                                                                                                                                                             Qmult(QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                          _args
                                                                                                                                                                                                                                                                                                                                                              .d_a0),
                                                                                                                                                                                                                                                                                                                                                      b->seq(
                                                                                                                                                                                                                                                                                                                                                          _args
                                                                                                                                                                                                                                                                                                                                                              .d_a0)),
                                                                                                                                                                                                                                                                                                                                   std::make_shared<
                                                                                                                                                                                                                                                                                                                                       Q>(
                                                                                                                                                                                                                                                                                                                                       Q{Z::zpos(Positive::xh()), Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                      Positive::xh())})))),
                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::inject_Q(std::make_shared<
                                                                                                                                                                                                                                                                                                                                        Q>(
                                                                                                                                                                                                                                                                                                          Q{
                                                                                                                                                                                                                                                                                                              Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                                      CMorphisms::subrelation_proper(([]()
                                                                                                                                                                                                                                                                                                                                          -> std::any {
                                                                                                                                                                                                                                                                                                                                       throw std::
                                                                                                                                                                                                                                                                                                                                           logic_error(
                                                                                                                                                                                                                                                                                                                                               "unreachable");
                                                                                                                                                                                                                                                                                                                                       return std::
                                                                                                                                                                                                                                                                                                                                           any{};
                                                                                                                                                                                                                                                                                                                                     })(),
                                                                                                                                                                                                                                                                                                                                     [](
                                                                                                                                                                                                                                                                                                                                         std::shared_ptr<CReal> x0, std::shared_ptr<CReal> x1,
                                                                                                                                                                                                                                                                                                                                         std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                             CReal>
                                                                                                                                                                                                                                                                                                                                             x2,
                                                                                                                                                                                                                                                                                                                                         std::shared_ptr<CReal>
                                                                                                                                                                                                                                                                                                                                             x3) {
                                                                                                                                                                                                                                                                                                                                       return ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                           CRealLt_morph()(
                                                                                                                                                                                                                                                                                                                                               x0,
                                                                                                                                                                                                                                                                                                                                               x1,
                                                                                                                                                                                                                                                                                                                                               x2,
                                                                                                                                                                                                                                                                                                                                               x3);
                                                                                                                                                                                                                                                                                                                                     },
                                                                                                                                                                                                                                                                                                                                     Unit::
                                                                                                                                                                                                                                                                                                                                         e_TT,
                                                                                                                                                                                                                                                                                                                                     CMorphisms::
                                                                                                                                                                                                                                                                                                                                         subrelation_respectful(([]()
                                                                                                                                                                                                                                                                                                                                                                     -> std::any {
                                                                                                                                                                                                                                                                                                                                                                  throw std::
                                                                                                                                                                                                                                                                                                                                                                      logic_error(
                                                                                                                                                                                                                                                                                                                                                                          "unreachable");
                                                                                                                                                                                                                                                                                                                                                                  return std::
                                                                                                                                                                                                                                                                                                                                                                      any{};
                                                                                                                                                                                                                                                                                                                                                                })(),
                                                                                                                                                                                                                                                                                                                                                                CMorphisms::subrelation_respectful(([]()
                                                                                                                                                                                                                                                                                                                                                                                                        -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                     throw std::
                                                                                                                                                                                                                                                                                                                                                                                                         logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                             "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                     return std::
                                                                                                                                                                                                                                                                                                                                                                                                         any{};
                                                                                                                                                                                                                                                                                                                                                                                                   })(),
                                                                                                                                                                                                                                                                                                                                                                                                   CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                       iffT_flip_arrow_subrelation)),
                                                                                                                                                                                                                                                                                                                                     ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                         CReal_plus(ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::CReal_opp(b), ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 a
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     ->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh())})))),
                                                                                                                                                                                                                                                                                                                                                    ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                        CReal_opp(
                                                                                                                                                                                                                                                                                                                                                            ConstructiveCauchyReals::inject_Q(QArith_base::Qmult(QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                        _args
                                                                                                                                                                                                                                                                                                                                                                                                                                            .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                    b->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                               .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                 std::
                                                                                                                                                                                                                                                                                                                                                                                                                     make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                         Q>(Q{Z::zpos(Positive::xh()), Positive::xo(Positive::xh())}))))))(
                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                              CReal_plus(
                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::CReal_opp(b), ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                             CReal_plus(ConstructiveCauchyReals::inject_Q(QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                                                                                            QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                               b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                            std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                Q>(Q{Z::zpos(Positive::xh()), Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                  Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                      xh())}))),
                                                                                                                                                                                                                                                                                                                                                                        ConstructiveCauchyReals::CReal_opp(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                               inject_Q(QArith_base::Qmult(QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                               a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                               b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                           std::
                                                                                                                                                                                                                                                                                                                                                                                                                                               make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                   Q>(
                                                                                                                                                                                                                                                                                                                                                                                                                                                   Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                       Z::zpos(Positive::xh()), Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        xh())})))))),
                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                              CReal_plus(ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                             std::
                                                                                                                                                                                                                                                                                                                                 make_shared<
                                                                                                                                                                                                                                                                                                                                     Q>(
                                                                                                                                                                                                                                                                                                                                     Q{Z::z0(),
                                                                                                                                                                                                                                                                                                                                       Positive::xh()})),
                                                                                                                                                                                                                                                                                                                         ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                             CReal_opp(
                                                                                                                                                                                                                                                                                                                                 ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                                                                                                                                                                       Qmult(
                                                                                                                                                                                                                                                                                                                                                                           QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                  _args
                                                                                                                                                                                                                                                                                                                                                                                                      .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                              b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                  _args
                                                                                                                                                                                                                                                                                                                                                                                                      .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                           std::
                                                                                                                                                                                                                                                                                                                                                                               make_shared<Q>(
                                                                                                                                                                                                                                                                                                                                                                                   Q{
                                                                                                                                                                                                                                                                                                                                                                                       Z::zpos(Positive::xh()), Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                    Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                        xh())}))))),
                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                              CReal_plus(
                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                      inject_Q(
                                                                                                                                                                                                                                                                                                                          std::
                                                                                                                                                                                                                                                                                                                              make_shared<
                                                                                                                                                                                                                                                                                                                                  Q>(
                                                                                                                                                                                                                                                                                                                                  Q{Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                      CReal_opp(ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                                                                                                                                                                      Qmult(QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                               b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                            std::
                                                                                                                                                                                                                                                                                                                                                                                make_shared<
                                                                                                                                                                                                                                                                                                                                                                                    Q>(
                                                                                                                                                                                                                                                                                                                                                                                    Q{Z::
                                                                                                                                                                                                                                                                                                                                                                                          zpos(Positive::xh()),
                                                                                                                                                                                                                                                                                                                                                                                      Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                          Positive::
                                                                                                                                                                                                                                                                                                                                                                                              xh())}))))),
                                                                                                                                                                                                                                                                                                          CMorphisms::
                                                                                                                                                                                                                                                                                                              subrelation_proper((
                                                                                                                                                                                                                                                                                                                                     []()
                                                                                                                                                                                                                                                                                                                                         -> std::
                                                                                                                                                                                                                                                                                                                                             any {
                                                                                                                                                                                                                                                                                                                                               throw std::
                                                                                                                                                                                                                                                                                                                                                   logic_error(
                                                                                                                                                                                                                                                                                                                                                       "unreachable");
                                                                                                                                                                                                                                                                                                                                               return std::
                                                                                                                                                                                                                                                                                                                                                   any{};
                                                                                                                                                                                                                                                                                                                                             })(),
                                                                                                                                                                                                                                                                                                                                 [](std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                        CReal>
                                                                                                                                                                                                                                                                                                                                        x0,
                                                                                                                                                                                                                                                                                                                                    std::shared_ptr<CReal> x1, std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
                                                                                                                                                                                                                                                                                                                                   return ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                       CRealLt_morph()(
                                                                                                                                                                                                                                                                                                                                           x0,
                                                                                                                                                                                                                                                                                                                                           x1,
                                                                                                                                                                                                                                                                                                                                           x2,
                                                                                                                                                                                                                                                                                                                                           x3);
                                                                                                                                                                                                                                                                                                                                 },
                                                                                                                                                                                                                                                                                                                                 Unit::
                                                                                                                                                                                                                                                                                                                                     e_TT,
                                                                                                                                                                                                                                                                                                                                 CMorphisms::subrelation_respectful(([]()
                                                                                                                                                                                                                                                                                                                                                                         -> std::any {
                                                                                                                                                                                                                                                                                                                                                                      throw std::
                                                                                                                                                                                                                                                                                                                                                                          logic_error(
                                                                                                                                                                                                                                                                                                                                                                              "unreachable");
                                                                                                                                                                                                                                                                                                                                                                      return std::
                                                                                                                                                                                                                                                                                                                                                                          any{};
                                                                                                                                                                                                                                                                                                                                                                    })(),
                                                                                                                                                                                                                                                                                                                                                                    CMorphisms::subrelation_respectful(([]() -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                 any {
                                                                                                                                                                                                                                                                                                                                                                                                                   throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                       logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                           "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                   return std::
                                                                                                                                                                                                                                                                                                                                                                                                                       any{};
                                                                                                                                                                                                                                                                                                                                                                                                                 })(),
                                                                                                                                                                                                                                                                                                                                                                                                       CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                           iffT_flip_arrow_subrelation)),
                                                                                                                                                                                                                                                                                                                                 ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                     CReal_plus(ConstructiveCauchyReals::CReal_opp(b), ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                           CReal_plus(
                                                                                                                                                                                                                                                                                                                                                                                               ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                   QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                       Qmult(QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                 a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                     _args
                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                 b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                     _args
                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                             std::
                                                                                                                                                                                                                                                                                                                                                                                                                 make_shared<Q>(Q{Z::zpos(Positive::xh()), Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                               xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       xh())}))),
                                                                                                                                                                                                                                                                                                                                                                                               ConstructiveCauchyReals::CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                   ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                       inject_Q(QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                           QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                               Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                         _args
                                                                                                                                                                                                                                                                                                                                                                                                                             .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                     b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                         _args
                                                                                                                                                                                                                                                                                                                                                                                                                             .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                           std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                               Q>(Q{Z::zpos(Positive::xh()), Positive::xo(Positive::xh())})))))))(ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::CReal_opp(b), ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 inject_Q(std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Z::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         z0(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         xh()}))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      CReal_plus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              inject_Q(std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Q>(Q{Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              CReal_opp(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            inject_Q(QArith_base::Qmult(QArith_base::Qplus(a
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               ->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Q>(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Q{Z::zpos(Positive::xh()), Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           xo(Positive::xh())}))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::CReal_plus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              std::make_shared<Q>(Q{Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                Qmult(QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         b->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Q>(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Q{Z::zpos(Positive::xh()), Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Positive::xh())}))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  CMorphisms::subrelation_proper(([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 [](std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            x0,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        x1,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            x2,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        x3) {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   return ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       CRealLt_morph()(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           x0,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           x1,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           x2,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           x3);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 },
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Unit::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     e_TT,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 CMorphisms::subrelation_respectful(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     ([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     CMorphisms::subrelation_respectful(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         ([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             iffT_flip_arrow_subrelation)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             b),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     ConstructiveCauchyReals::inject_Q(std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Z::z0(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             xh()}))))(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               b),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Q>(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Q{Z::z0(), Positive::xh()})),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           ConstructiveCauchyReals::CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Qmult(QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         xh())}))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       ConstructiveCauchyReals::CReal_plus(ConstructiveCauchyReals::inject_Q(std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Q>(Q{Z::z0(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      xh()})),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               CReal_opp(ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       xh())}))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       CMorphisms::Reflexive_partial_app_morphism(([]() -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  CMorphisms::subrelation_proper(([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 [](std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        x0,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    std::shared_ptr<CReal> x1,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   return ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       CRealLt_morph()(x0, x1, x2, x3);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 },
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Unit::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     e_TT,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 CMorphisms::subrelation_respectful(([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    CMorphisms::subrelation_respectful(([]() -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           iffT_flip_arrow_subrelation))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          b))(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  CReal_plus(ConstructiveCauchyReals::inject_Q(std::make_shared<Q>(Q{Z::z0(), Positive::xh()})), ConstructiveCauchyReals::CReal_opp(ConstructiveCauchyReals::inject_Q(QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          xh())}))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ConstructiveCauchyReals::CReal_opp(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Qmult(QArith_base::Qplus(a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   std::make_shared<Q>(Q{Z::zpos(Positive::xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             xo(Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    xh())})))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              CMorphisms::Reflexive_partial_app_morphism(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       -> std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      subrelation_proper(([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         [](std::shared_ptr<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                CReal>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                x0,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            std::shared_ptr<CReal> x1, std::shared_ptr<CReal> x2, std::shared_ptr<CReal> x3) {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           return ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               CRealLt_morph()(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   x0, x1, x2, x3);
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         },
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Unit::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             e_TT,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             subrelation_respectful(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 ([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   throw std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       logic_error(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           "unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     subrelation_respectful(([]()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 -> std::any {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              throw std::logic_error("unreachable");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              return std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  any{};
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            })(),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            CMorphisms::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                iffT_flip_arrow_subrelation))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          b))(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Qplus(a->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                b
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Q>(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Q{Z::zpos(Positive::xh()), Positive::xo(Positive::xh())})))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Qopp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      a->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      b->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      make_shared<Q>(Q{Z::zpos(Positive::xh()), Positive::xo(Positive::xh())})))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ConstructiveCauchyReals::CReal_le_lt_trans(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 b),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         ConstructiveCauchyReals::inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Qplus(ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               b)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               ->seq(_args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       QArith_base::Qpower(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Z::zpos(Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       xh())),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   xh()}),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               .d_a0))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             inject_Q(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 QArith_base::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Qopp(QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh())})))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         ConstructiveCauchyReals::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             inject_Q_lt(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     ConstructiveCauchyReals::CReal_opp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         b)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         ->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     QArith_base::Qpower(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         std::make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Z::zpos(Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh())),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 xh()}),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 QArith_base::Qopp(QArith_base::Qmult(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     QArith_base::Qplus(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         a->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         b->seq(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _args
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 .d_a0)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     std::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         make_shared<
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Q>(Q{
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Z::zpos(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh()),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Positive::xo(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 Positive::
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     xh())})))))))))))))));
                      }},
          h->v());
}

std::shared_ptr<Positive>
ConstructiveRcomplete::CReal_from_cauchy_cm(const std::shared_ptr<Z> &n) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Positive> {
                   return Positive::xh();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Positive> {
                   return Positive::xh();
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Positive> {
                   return _args.d_a0;
                 }},
      n->v());
}

std::shared_ptr<SigT<std::shared_ptr<Positive>, CRealLt>>
ConstructiveRcomplete::Rup_pos(std::shared_ptr<CReal> x) {
  std::shared_ptr<SigT<std::shared_ptr<Z>,
                       std::pair<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::shared_ptr<Sig<std::shared_ptr<Z>>>>>>
      s = ConstructiveCauchyRealsMult::CRealArchimedean(x);
  return std::visit(
      Overloaded{[&](const typename SigT<
                     std::shared_ptr<Z>,
                     std::pair<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                               std::shared_ptr<Sig<std::shared_ptr<Z>>>>>::
                         ExistT _args)
                     -> std::shared_ptr<
                         SigT<std::shared_ptr<Positive>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
        std::shared_ptr<Sig<std::shared_ptr<Z>>> c = _args.d_a1.first;
        std::shared_ptr<Sig<std::shared_ptr<Z>>> _x = _args.d_a1.second;
        return std::visit(
            Overloaded{
                [&](const typename Z::Z0 _args0) -> auto {
                  return SigT<std::shared_ptr<Positive>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                      existt(
                          Positive::xh(),
                          ConstructiveCauchyReals::CReal_lt_trans(
                              x,
                              ConstructiveCauchyReals::inject_Q(
                                  std::make_shared<Q>(
                                      Q{Z::z0(), Positive::xh()})),
                              ConstructiveCauchyReals::inject_Q(
                                  std::make_shared<Q>(Q{Z::zpos(Positive::xh()),
                                                        Positive::xh()})),
                              c, ConstructiveCauchyReals::CRealLt_0_1));
                },
                [&](const typename Z::Zpos _args0) -> auto {
                  return SigT<std::shared_ptr<Positive>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                      existt(_args0.d_a0, c);
                },
                [&](const typename Z::Zneg _args0) -> auto {
                  return SigT<std::shared_ptr<Positive>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                      existt(
                          Positive::xh(),
                          ConstructiveCauchyReals::CReal_lt_trans(
                              x,
                              ConstructiveCauchyReals::inject_Q(
                                  std::make_shared<Q>(
                                      Q{Z::zneg(_args0.d_a0), Positive::xh()})),
                              ConstructiveCauchyReals::inject_Q(
                                  std::make_shared<Q>(Q{Z::zpos(Positive::xh()),
                                                        Positive::xh()})),
                              c,
                              ConstructiveCauchyReals::CReal_lt_trans(
                                  ConstructiveCauchyReals::inject_Q(
                                      std::make_shared<Q>(
                                          Q{Z::zneg(_args0.d_a0),
                                            Positive::xh()})),
                                  ConstructiveCauchyReals::inject_Q(
                                      std::make_shared<Q>(
                                          Q{Z::z0(), Positive::xh()})),
                                  ConstructiveCauchyReals::inject_Q(
                                      std::make_shared<Q>(
                                          Q{Z::zpos(Positive::xh()),
                                            Positive::xh()})),
                                  ConstructiveCauchyReals::inject_Q_lt(
                                      std::make_shared<Q>(
                                          Q{Z::zneg(_args0.d_a0),
                                            Positive::xh()}),
                                      std::make_shared<Q>(
                                          Q{Z::z0(), Positive::xh()})),
                                  ConstructiveCauchyReals::CRealLt_0_1)));
                }},
            std::move(_args.d_a0)->v());
      }},
      std::move(s)->v());
}

std::shared_ptr<Sum<CRealLt, CRealLt>>
ConstructiveRcomplete::CRealLtDisjunctEpsilon(std::shared_ptr<CReal> a,
                                              std::shared_ptr<CReal> b,
                                              std::shared_ptr<CReal> c,
                                              std::shared_ptr<CReal> d) {
  std::shared_ptr<Sig<std::shared_ptr<Z>>> h0 =
      ConstructiveExtra::constructive_indefinite_ground_description_Z(
          [=](std::shared_ptr<Z> n) mutable {
            bool s = QArith_base::Qlt_le_dec(
                QArith_base::Qmult(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    QArith_base::Qpower(
                        std::make_shared<Q>(
                            Q{Z::zpos(Positive::xo(Positive::xh())),
                              Positive::xh()}),
                        n)),
                QArith_base::Qminus(b->seq(n), a->seq(n)));
            if (s) {
              return true;
            } else {
              bool s0 = QArith_base::Qlt_le_dec(
                  QArith_base::Qmult(
                      std::make_shared<Q>(
                          Q{Z::zpos(Positive::xo(Positive::xh())),
                            Positive::xh()}),
                      QArith_base::Qpower(
                          std::make_shared<Q>(
                              Q{Z::zpos(Positive::xo(Positive::xh())),
                                Positive::xh()}),
                          n)),
                  QArith_base::Qminus(d->seq(n), c->seq(n)));
              if (s0) {
                return true;
              } else {
                return false;
              }
            }
          });
  return std::visit(
      Overloaded{[&](const typename Sig<std::shared_ptr<Z>>::Exist _args)
                     -> std::shared_ptr<
                         Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                             std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
        bool s = QArith_base::Qlt_le_dec(
            QArith_base::Qmult(
                std::make_shared<Q>(
                    Q{Z::zpos(Positive::xo(Positive::xh())), Positive::xh()}),
                QArith_base::Qpower(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    _args.d_a0)),
            QArith_base::Qminus(std::move(b)->seq(_args.d_a0),
                                std::move(a)->seq(_args.d_a0)));
        if (std::move(s)) {
          return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                     std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
              inl(Sig<std::shared_ptr<Z>>::exist(_args.d_a0));
        } else {
          return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                     std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
              inr(Sig<std::shared_ptr<Z>>::exist(_args.d_a0));
        }
      }},
      std::move(h0)->v());
}

__attribute__((pure)) RbaseSymbolsImpl::R Raxioms::INR(const unsigned int n) {
  if (n <= 0) {
    return ::IZR(Z::z0());
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return ::IZR(Z::zpos(Positive::xh()));
    } else {
      unsigned int _x = n0 - 1;
      return RbaseSymbolsImpl::Rplus(Raxioms::INR(n0),
                                     ::IZR(Z::zpos(Positive::xh())));
    }
  }
}

__attribute__((pure)) bool RIneq::Rlt_dec(const RbaseSymbolsImpl::R r1,
                                          const RbaseSymbolsImpl::R r2) {
  std::shared_ptr<Sumor<bool>> s = ::total_order_T(r1, r2);
  return std::visit(
      Overloaded{[](const typename Sumor<bool>::Inleft _args) -> bool {
                   if (_args.d_a0) {
                     return true;
                   } else {
                     return false;
                   }
                 },
                 [](const typename Sumor<bool>::Inright _args) -> bool {
                   return false;
                 }},
      std::move(s)->v());
}

__attribute__((pure)) bool RIneq::Rle_dec(const RbaseSymbolsImpl::R r1,
                                          const RbaseSymbolsImpl::R r2) {
  bool s = RIneq::Rlt_dec(r2, r1);
  if (std::move(s)) {
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) RbaseSymbolsImpl::R
RIneq::Rsqr(const RbaseSymbolsImpl::R r) {
  return RbaseSymbolsImpl::Rmult(r, r);
}

__attribute__((pure)) RbaseSymbolsImpl::R
Rpow_def::pow0(const RbaseSymbolsImpl::R r, const unsigned int n) {
  if (n <= 0) {
    return ::IZR(Z::zpos(Positive::xh()));
  } else {
    unsigned int n0 = n - 1;
    return RbaseSymbolsImpl::Rmult(r, Rpow_def::pow0(r, n0));
  }
}

__attribute__((pure)) bool Rbasic_fun::Rcase_abs(const RbaseSymbolsImpl::R r) {
  bool x = RIneq::Rle_dec(::IZR(Z::z0()), r);
  if (std::move(x)) {
    return false;
  } else {
    return true;
  }
}

__attribute__((pure)) bool
Rsqrt_def::cond_positivity(const RbaseSymbolsImpl::R x) {
  if (RIneq::Rle_dec(::IZR(Z::z0()), x)) {
    return true;
  } else {
    return false;
  }
}

std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
Rsqrt_def::Rsqrt_exists(const RbaseSymbolsImpl::R y) {
  std::function<RbaseSymbolsImpl::R(RbaseSymbolsImpl::R)> f =
      [=](RbaseSymbolsImpl::R x) mutable {
        return ::Rminus(RIneq::Rsqr(x), y);
      };
  std::shared_ptr<Sumor<bool>> s =
      ::total_order_T(y, ::IZR(Z::zpos(Positive::xh())));
  return std::visit(
      Overloaded{
          [&](const typename Sumor<bool>::Inleft _args)
              -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
            if (_args.d_a0) {
              std::shared_ptr<Sig<RbaseSymbolsImpl::R>> x = Rsqrt_def::IVT_cor(
                  f, ::IZR(Z::z0()), ::IZR(Z::zpos(Positive::xh())));
              return [&](void) {
                if (std::move(x).use_count() == 1 &&
                    std::move(x)->v().index() == 0) {
                  auto &_rf = std::get<0>(std::move(x)->v_mut());
                  T1 x0 = std::move(_rf.d_a0);
                  _rf.d_a0 = std::move(x0);
                  return std::move(x);
                } else {
                  return std::visit(
                      Overloaded{
                          [](const typename Sig<RbaseSymbolsImpl::R>::Exist
                                 _args0) -> auto {
                            return Sig<RbaseSymbolsImpl::R>::exist(_args0.d_a0);
                          }},
                      std::move(x)->v());
                }
              }();
            } else {
              return Sig<RbaseSymbolsImpl::R>::exist(
                  ::IZR(Z::zpos(Positive::xh())));
            }
          },
          [&](const typename Sumor<bool>::Inright _args)
              -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
            std::shared_ptr<Sig<RbaseSymbolsImpl::R>> x =
                Rsqrt_def::IVT_cor(f, ::IZR(Z::z0()), y);
            return [&](void) {
              if (std::move(x).use_count() == 1 &&
                  std::move(x)->v().index() == 0) {
                auto &_rf = std::get<0>(std::move(x)->v_mut());
                T1 x0 = std::move(_rf.d_a0);
                _rf.d_a0 = std::move(x0);
                return std::move(x);
              } else {
                return std::visit(
                    Overloaded{[](const typename Sig<RbaseSymbolsImpl::R>::Exist
                                      _args0) -> auto {
                      return Sig<RbaseSymbolsImpl::R>::exist(_args0.d_a0);
                    }},
                    std::move(x)->v());
              }
            }();
          }},
      std::move(s)->v());
}

__attribute__((pure)) RbaseSymbolsImpl::R
Rsqrt_def::Rsqrt(const std::shared_ptr<nonnegreal> &y) {
  return std::visit(
      Overloaded{[](const typename Sig<RbaseSymbolsImpl::R>::Exist _args)
                     -> RbaseSymbolsImpl::R { return _args.d_a0; }},
      Rsqrt_def::Rsqrt_exists(y->nonneg)->v());
}

__attribute__((pure)) RbaseSymbolsImpl::R
R_sqrt::sqrt(const RbaseSymbolsImpl::R x) {
  if (Rbasic_fun::Rcase_abs(x)) {
    return ::IZR(Z::z0());
  } else {
    return Rsqrt_def::Rsqrt(std::make_shared<nonnegreal>(nonnegreal{x}));
  }
}
