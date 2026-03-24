#include <fold_sequence_state_trace.h>

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

__attribute__((pure)) bool PeanoNat::eqb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
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
            return Positive::ctor::XO_(succ(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XI_(_args.d_a0);
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XO_(Positive::ctor::XH_());
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
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XI_(add(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XO _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XO_(add(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XH _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XI_(_args.d_a0);
                    }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(_args0.d_a0);
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(Positive::ctor::XH_());
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
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(Positive::ctor::XH_());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XI_(Positive::ctor::XO_(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XI_(pred_double(_args.d_a0));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XH_();
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return add(y, Positive::ctor::XO_(mul(_args.d_a0, y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XO_(mul(_args.d_a0, std::move(y)));
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
    return Positive::ctor::XH_();
  } else {
    unsigned int x = n - 1;
    return succ(of_succ_nat(x));
  }
}

std::shared_ptr<Positive> Coq_Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XO_(succ(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XI_(_args.d_a0);
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XO_(Positive::ctor::XH_());
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
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XI_(add(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XO _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XO_(add(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Positive::XH _args0)
                        -> std::shared_ptr<Positive> {
                      return Positive::ctor::XI_(_args.d_a0);
                    }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(_args0.d_a0);
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(Positive::ctor::XH_());
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
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(
                                 add_carry(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(
                                 add(_args.d_a0, _args0.d_a0));
                           },
                           [&](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XO _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(_args0.d_a0));
                           },
                           [](const typename Positive::XH _args0)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(Positive::ctor::XH_());
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
            return Positive::ctor::XI_(Positive::ctor::XO_(_args.d_a0));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XI_(pred_double(_args.d_a0));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XH_();
          }},
      x->v());
}

std::shared_ptr<mask>
Coq_Pos::succ_double_mask(const std::shared_ptr<mask> &x) {
  return std::visit(
      Overloaded{[](const typename mask::IsNul _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsPos_(Positive::ctor::XH_());
                 },
                 [](const typename mask::IsPos _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsPos_(Positive::ctor::XI_(_args.d_a0));
                 },
                 [](const typename mask::IsNeg _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsNeg_();
                 }},
      x->v());
}

std::shared_ptr<mask> Coq_Pos::double_mask(const std::shared_ptr<mask> &x) {
  return std::visit(
      Overloaded{[](const typename mask::IsNul _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsNul_();
                 },
                 [](const typename mask::IsPos _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsPos_(Positive::ctor::XO_(_args.d_a0));
                 },
                 [](const typename mask::IsNeg _args) -> std::shared_ptr<mask> {
                   return mask::ctor::IsNeg_();
                 }},
      x->v());
}

std::shared_ptr<mask>
Coq_Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<mask> {
            return mask::ctor::IsPos_(
                Positive::ctor::XO_(Positive::ctor::XO_(_args.d_a0)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<mask> {
            return mask::ctor::IsPos_(
                Positive::ctor::XO_(pred_double(_args.d_a0)));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<mask> {
            return mask::ctor::IsNul_();
          }},
      x->v());
}

std::shared_ptr<mask> Coq_Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                        const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<mask> {
            return std::visit(Overloaded{[&](const typename Positive::XI _args0)
                                             -> std::shared_ptr<mask> {
                                           return double_mask(sub_mask(
                                               _args.d_a0, _args0.d_a0));
                                         },
                                         [&](const typename Positive::XO _args0)
                                             -> std::shared_ptr<mask> {
                                           return succ_double_mask(sub_mask(
                                               _args.d_a0, _args0.d_a0));
                                         },
                                         [&](const typename Positive::XH _args0)
                                             -> std::shared_ptr<mask> {
                                           return mask::ctor::IsPos_(
                                               Positive::ctor::XO_(_args.d_a0));
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
                             return mask::ctor::IsPos_(pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<mask> {
            return std::visit(Overloaded{[](const typename Positive::XI _args0)
                                             -> std::shared_ptr<mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::XO _args0)
                                             -> std::shared_ptr<mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::XH _args0)
                                             -> std::shared_ptr<mask> {
                                           return mask::ctor::IsNul_();
                                         }},
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
                             return mask::ctor::IsPos_(pred_double(_args.d_a0));
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
            return mask::ctor::IsNeg_();
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::sub(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [](const typename mask::IsNul _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XH_();
          },
          [](const typename mask::IsPos _args) -> std::shared_ptr<Positive> {
            return _args.d_a0;
          },
          [](const typename mask::IsNeg _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XH_();
          }},
      sub_mask(x, y)->v());
}

std::shared_ptr<Positive> Coq_Pos::mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            return add(y, Positive::ctor::XO_(mul(_args.d_a0, y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XO_(mul(_args.d_a0, std::move(y)));
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
    return std::make_pair(Positive::ctor::XH_(),
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
                                a, std::make_pair(Positive::ctor::XH_(),
                                                  Positive::ctor::XH_()));
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
                                std::make_pair(
                                    aa, add(aa, Positive::ctor::XO_(ba))));
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
                                std::make_pair(add(bb, Positive::ctor::XO_(ab)),
                                               bb));
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
                            std::move(g),
                            std::make_pair(aa, Positive::ctor::XO_(bb)));
                      },
                      [&](const typename Positive::XH _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        return std::make_pair(
                            Positive::ctor::XH_(),
                            std::make_pair(a, Positive::ctor::XH_()));
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
                            std::move(g),
                            std::make_pair(Positive::ctor::XO_(aa), bb));
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
                        return std::make_pair(Positive::ctor::XO_(g), p);
                      },
                      [&](const typename Positive::XH _args0)
                          -> std::pair<std::shared_ptr<Positive>,
                                       std::pair<std::shared_ptr<Positive>,
                                                 std::shared_ptr<Positive>>> {
                        return std::make_pair(
                            Positive::ctor::XH_(),
                            std::make_pair(a, Positive::ctor::XH_()));
                      }},
                  b->v());
            },
            [&](const typename Positive::XH _args)
                -> std::pair<std::shared_ptr<Positive>,
                             std::pair<std::shared_ptr<Positive>,
                                       std::shared_ptr<Positive>>> {
              return std::make_pair(
                  Positive::ctor::XH_(),
                  std::make_pair(Positive::ctor::XH_(), std::move(b)));
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
    return Positive::ctor::XH_();
  } else {
    unsigned int x = n - 1;
    if (x <= 0) {
      return Positive::ctor::XH_();
    } else {
      unsigned int _x = x - 1;
      return succ(of_nat(x));
    }
  }
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::XO_(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::XO_(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::XH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::XI_(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Pos::pred_double(_args.d_a0));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::XH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Pos::pred_double(_args.d_a0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::XI_(_args.d_a0));
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
                             return Z::ctor::Zpos_(
                                 Positive::ctor::XO_(_args.d_a0));
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
                             return Z::ctor::Zpos_(
                                 Pos::pred_double(_args.d_a0));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::XI _args0)
                        -> std::shared_ptr<Z> {
                      return Z::ctor::Zneg_(Positive::ctor::XO_(_args0.d_a0));
                    },
                    [](const typename Positive::XO _args0)
                        -> std::shared_ptr<Z> {
                      return Z::ctor::Zneg_(Pos::pred_double(_args0.d_a0));
                    },
                    [](const typename Positive::XH _args0)
                        -> std::shared_ptr<Z> { return Z::ctor::Z0_(); }},
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
                          return Z::ctor::Zpos_(
                              Pos::add(_args.d_a0, _args0.d_a0));
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
                          return Z::ctor::Zneg_(
                              Pos::add(_args.d_a0, _args0.d_a0));
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
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(_args.d_a0);
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(_args.d_a0);
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
            return Z::ctor::Z0_();
          },
          [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Zpos_(Pos::mul(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Zneg_(Pos::mul(_args.d_a0, _args0.d_a0));
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Zneg_(Pos::mul(_args.d_a0, _args0.d_a0));
                    },
                    [&](const typename Z::Zneg _args0) -> std::shared_ptr<Z> {
                      return Z::ctor::Zpos_(Pos::mul(_args.d_a0, _args0.d_a0));
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
    return Z::ctor::Z0_();
  } else {
    unsigned int n0 = n - 1;
    return Z::ctor::Zpos_(Pos::of_succ_nat(n0));
  }
}

std::shared_ptr<Positive> BinInt::to_pos(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Positive> {
                   return Positive::ctor::XH_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Positive> {
                   return _args.d_a0;
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Positive> {
                   return Positive::ctor::XH_();
                 }},
      z->v());
}

std::shared_ptr<Z> BinInt::sgn(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::XH_());
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::XH_());
                 }},
      z->v());
}

std::shared_ptr<Z> BinInt::abs(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(_args.d_a0);
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(_args.d_a0);
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
            return std::make_pair(
                BinInt::abs(b), std::make_pair(Z::ctor::Z0_(), BinInt::sgn(b)));
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
                          std::make_pair(BinInt::sgn(a), Z::ctor::Z0_()));
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
                      return std::make_pair(Z::ctor::Zpos_(std::move(g)),
                                            std::make_pair(Z::ctor::Zpos_(aa),
                                                           Z::ctor::Zpos_(bb)));
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
                      return std::make_pair(Z::ctor::Zpos_(std::move(g)),
                                            std::make_pair(Z::ctor::Zpos_(aa),
                                                           Z::ctor::Zneg_(bb)));
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
                          std::make_pair(BinInt::sgn(a), Z::ctor::Z0_()));
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
                      return std::make_pair(Z::ctor::Zpos_(std::move(g)),
                                            std::make_pair(Z::ctor::Zneg_(aa),
                                                           Z::ctor::Zpos_(bb)));
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
                      return std::make_pair(Z::ctor::Zpos_(std::move(g)),
                                            std::make_pair(Z::ctor::Zneg_(aa),
                                                           Z::ctor::Zneg_(bb)));
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
  return Rabst(Rrepr(x)->CReal_plus(Rrepr(y)));
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
  return Rabst(Rrepr(x)->CReal_opp());
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
      RbaseSymbolsImpl::Rrepr(r1)->CRealLt_lpo_dec(
          RbaseSymbolsImpl::Rrepr(r2), [](auto &&d_a0) -> decltype(auto) {
            return sig_forall_dec(std::forward<decltype(d_a0)>(d_a0));
          });
  return std::visit(
      Overloaded{
          [](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::any>::Inl _args)
              -> std::shared_ptr<Sumor<bool>> {
            return Sumor<bool>::ctor::Inleft_(true);
          },
          [&](const typename Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                 std::any>::Inr _args)
              -> std::shared_ptr<Sumor<bool>> {
            std::shared_ptr<
                Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>>
                s0 = RbaseSymbolsImpl::Rrepr(r2)->CRealLt_lpo_dec(
                    RbaseSymbolsImpl::Rrepr(r1),
                    [](auto &&d_a0) -> decltype(auto) {
                      return sig_forall_dec(std::forward<decltype(d_a0)>(d_a0));
                    });
            return std::visit(
                Overloaded{
                    [](const typename Sum<
                        std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::Inl
                           _args0) -> std::shared_ptr<Sumor<bool>> {
                      return Sumor<bool>::ctor::Inright_();
                    },
                    [](const typename Sum<
                        std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::Inr
                           _args0) -> std::shared_ptr<Sumor<bool>> {
                      return Sumor<bool>::ctor::Inleft_(false);
                    }},
                std::move(s0)->v());
          }},
      std::move(s)->v());
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::line_through(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2) {
  RbaseSymbolsImpl::R x1 = p1.first;
  RbaseSymbolsImpl::R y1 = p1.second;
  RbaseSymbolsImpl::R x2 = p2.first;
  RbaseSymbolsImpl::R y2 = p2.second;
  if (RIneq::Req_dec_T(x1, x2)) {
    return std::make_shared<FoldSequenceStateTraceCase::Line>(
        Line{::IZR(Z::ctor::Zpos_(Positive::ctor::XH_())),
             ::IZR(Z::ctor::Z0_()), RbaseSymbolsImpl::Ropp(x1)});
  } else {
    RbaseSymbolsImpl::R a = ::Rminus(y1, y2);
    RbaseSymbolsImpl::R b = ::Rminus(x2, x1);
    RbaseSymbolsImpl::R c = ::Rminus(RbaseSymbolsImpl::Rmult(x1, y2),
                                     RbaseSymbolsImpl::Rmult(x2, y1));
    return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
  }
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::perp_bisector(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2) {
  RbaseSymbolsImpl::R x1 = p1.first;
  RbaseSymbolsImpl::R y1 = p1.second;
  RbaseSymbolsImpl::R x2 = p2.first;
  RbaseSymbolsImpl::R y2 = p2.second;
  if (RIneq::Req_dec_T(x1, x2)) {
    if (RIneq::Req_dec_T(y1, y2)) {
      return std::make_shared<FoldSequenceStateTraceCase::Line>(
          Line{::IZR(Z::ctor::Zpos_(Positive::ctor::XH_())),
               ::IZR(Z::ctor::Z0_()), RbaseSymbolsImpl::Ropp(x1)});
    } else {
      RbaseSymbolsImpl::R a = ::IZR(Z::ctor::Z0_());
      RbaseSymbolsImpl::R b = RbaseSymbolsImpl::Rmult(
          ::IZR(Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XH_()))),
          ::Rminus(y2, y1));
      RbaseSymbolsImpl::R c = ::Rminus(
          ::Rminus(RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::Rmult(x1, x1),
                                           RbaseSymbolsImpl::Rmult(y1, y1)),
                   RbaseSymbolsImpl::Rmult(x2, x2)),
          RbaseSymbolsImpl::Rmult(y2, y2));
      return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
    }
  } else {
    RbaseSymbolsImpl::R a = RbaseSymbolsImpl::Rmult(
        ::IZR(Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XH_()))),
        ::Rminus(x2, x1));
    RbaseSymbolsImpl::R b = RbaseSymbolsImpl::Rmult(
        ::IZR(Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XH_()))),
        ::Rminus(y2, y1));
    RbaseSymbolsImpl::R c = ::Rminus(
        ::Rminus(RbaseSymbolsImpl::Rplus(RbaseSymbolsImpl::Rmult(x1, x1),
                                         RbaseSymbolsImpl::Rmult(y1, y1)),
                 RbaseSymbolsImpl::Rmult(x2, x2)),
        RbaseSymbolsImpl::Rmult(y2, y2));
    return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
  }
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::perp_through(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p,
    std::shared_ptr<FoldSequenceStateTraceCase::Line> l) {
  RbaseSymbolsImpl::R x = p.first;
  RbaseSymbolsImpl::R y = p.second;
  RbaseSymbolsImpl::R c = ::Rminus(RbaseSymbolsImpl::Rmult(l->A, std::move(y)),
                                   RbaseSymbolsImpl::Rmult(l->B, x));
  return std::make_shared<FoldSequenceStateTraceCase::Line>(
      Line{l->B, RbaseSymbolsImpl::Ropp(l->A), c});
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O1(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2) {
  return Fold::ctor::Fold_line_ctor_(
      line_through(std::move(p1), std::move(p2)));
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O2(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2) {
  return Fold::ctor::Fold_line_ctor_(
      perp_bisector(std::move(p1), std::move(p2)));
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O4(
    const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p,
    std::shared_ptr<FoldSequenceStateTraceCase::Line> l) {
  return Fold::ctor::Fold_line_ctor_(perp_through(std::move(p), std::move(l)));
}

std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState>
FoldSequenceStateTraceCase::add_fold_to_state(
    std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> st,
    const std::shared_ptr<FoldSequenceStateTraceCase::FoldStep> &step) {
  std::shared_ptr<FoldSequenceStateTraceCase::Line> new_line =
      step->execute_fold_step();
  return std::make_shared<FoldSequenceStateTraceCase::ConstructionState>(
      ConstructionState{
          st->state_points,
          List<std::shared_ptr<FoldSequenceStateTraceCase::Line>>::ctor::Cons_(
              std::move(new_line), st->state_lines)});
}

std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState>
FoldSequenceStateTraceCase::execute_sequence(
    std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> st,
    const std::shared_ptr<
        List<std::shared_ptr<FoldSequenceStateTraceCase::FoldStep>>> &seq0) {
  return std::visit(
      Overloaded{
          [&](const typename List<
              std::shared_ptr<FoldSequenceStateTraceCase::FoldStep>>::Nil _args)
              -> std::shared_ptr<
                  FoldSequenceStateTraceCase::ConstructionState> {
            return std::move(st);
          },
          [&](const typename List<std::shared_ptr<
                  FoldSequenceStateTraceCase::FoldStep>>::Cons _args)
              -> std::shared_ptr<
                  FoldSequenceStateTraceCase::ConstructionState> {
            return execute_sequence(
                add_fold_to_state(std::move(st), _args.d_a0), _args.d_a1);
          }},
      seq0->v());
}

__attribute__((pure)) unsigned int
FoldSequenceStateTraceCase::line_count_after_sample_sequence(
    const std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> &st) {
  return execute_sequence(st, sample_sequence)->state_lines->length();
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

std::shared_ptr<Z> ConstructiveExtra::Z_inj_nat_rev(const unsigned int n) {
  if (n <= 0) {
    return Z::ctor::Z0_();
  } else {
    unsigned int _x = n - 1;
    return std::visit(
        Overloaded{[](const typename Positive::XI _args) -> std::shared_ptr<Z> {
                     return Z::ctor::Zneg_(Coq_Pos::succ(_args.d_a0));
                   },
                   [](const typename Positive::XO _args) -> std::shared_ptr<Z> {
                     return Z::ctor::Zpos_(_args.d_a0);
                   },
                   [](const typename Positive::XH _args) -> std::shared_ptr<Z> {
                     return Z::ctor::Zneg_(Positive::ctor::XH_());
                   }},
        Coq_Pos::of_nat(n)->v());
  }
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
            return Positive::ctor::XH_();
          }},
      p->v());
}

std::shared_ptr<ConstructiveCauchyReals::CReal>
ConstructiveCauchyReals::inject_Q(std::shared_ptr<Q> q) {
  return std::make_shared<ConstructiveCauchyReals::CReal>(
      CReal{[=](std::shared_ptr<Z> _x) mutable { return q; },
            q->Qbound_ltabs_ZExp2()});
}

__attribute__((pure)) ClassicalDedekindReals::DReal
ClassicalDedekindReals::DRealAbstr(std::shared_ptr<CReal> x) {
  std::function<bool(std::shared_ptr<Q>, unsigned int)> h =
      [=](std::shared_ptr<Q> q, unsigned int n) mutable {
        bool s =
            q->Qplus(std::make_shared<Q>(Q{Z::ctor::Zpos_(Positive::ctor::XO_(
                                               Positive::ctor::XH_())),
                                           Positive::ctor::XH_()})
                         ->Qpower(BinInt::opp(BinInt::of_nat(n))))
                ->Qlt_le_dec(x->seq(BinInt::opp(BinInt::of_nat(n))));
        if (std::move(s)) {
          return false;
        } else {
          return true;
        }
      };
  return Sig<std::function<bool(
      std::shared_ptr<Q>)>>::ctor::Exist_([=](std::shared_ptr<Q> q) mutable {
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
                  _args0.d_a0
                      ->Qminus(std::visit(
                          Overloaded{
                              [](const typename Sig<std::shared_ptr<Q>>::Exist
                                     _args1) -> auto { return _args1.d_a0; }},
                          ClassicalDedekindReals::lowerCutBelow(_args.d_a0)
                              ->v()))
                      ->Qarchimedean();
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
            return Sig<std::shared_ptr<Q>>::ctor::Exist_(_args.d_a0);
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
  return ClassicalDedekindReals::CReal_of_DReal_seq(
             x, Z::ctor::Zneg_(Positive::ctor::XH_()))
      ->Qabs()
      ->Qplus(std::make_shared<Q>(
          Q{Z::ctor::Zpos_(Positive::ctor::XO_(Positive::ctor::XH_())),
            Positive::ctor::XH_()}))
      ->Qbound_lt_ZExp2();
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
  return x
      ->seq(BinInt::sub(BinInt::sub(n, y->scale),
                        Z::ctor::Zpos_(Positive::ctor::XH_())))
      ->Qmult(y->seq(BinInt::sub(BinInt::sub(n, x->scale),
                                 Z::ctor::Zpos_(Positive::ctor::XH_()))));
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

__attribute__((pure)) bool RIneq::Req_dec_T(const RbaseSymbolsImpl::R r1,
                                            const RbaseSymbolsImpl::R r2) {
  std::shared_ptr<Sumor<bool>> s = ::total_order_T(r1, r2);
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
