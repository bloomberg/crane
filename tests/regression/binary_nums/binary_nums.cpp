#include <binary_nums.h>

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

std::shared_ptr<Positive> Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XO_(succ(std::move(p)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XI_(std::move(p));
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(succ(std::move(q)));
                           },
                           [](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(std::move(q));
                           },
                           [](const typename Positive::XH _args)
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(succ(std::move(q)));
                           },
                           [](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(succ(std::move(q)));
                           },
                           [](const typename Positive::XH _args)
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XI_(Positive::ctor::XO_(std::move(p)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XI_(pred_double(std::move(p)));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::XH_();
          }},
      x->v());
}

std::shared_ptr<N> Pos::pred_N(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::XI _args) -> std::shared_ptr<N> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return N::ctor::Npos_(Positive::ctor::XO_(std::move(p)));
                 },
                 [](const typename Positive::XO _args) -> std::shared_ptr<N> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return N::ctor::Npos_(pred_double(std::move(p)));
                 },
                 [](const typename Positive::XH _args) -> std::shared_ptr<N> {
                   return N::ctor::N0_();
                 }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsPos_(Positive::ctor::XH_());
          },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return mask::ctor::IsPos_(Positive::ctor::XI_(std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNul_(); },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return mask::ctor::IsPos_(Positive::ctor::XO_(std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::XI _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return mask::ctor::IsPos_(
                Positive::ctor::XO_(Positive::ctor::XO_(std::move(p))));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return mask::ctor::IsPos_(
                Positive::ctor::XO_(pred_double(std::move(p))));
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsNul_();
          }},
      x->v());
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return succ_double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsPos_(
                                 Positive::ctor::XO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::XO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::XH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(Overloaded{[](const typename Positive::XI _args)
                                             -> std::shared_ptr<Pos::mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::XO _args)
                                             -> std::shared_ptr<Pos::mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::XH _args)
                                             -> std::shared_ptr<Pos::mask> {
                                           return mask::ctor::IsNul_();
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::XO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::XH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return succ_double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return double_pred_mask(std::move(p));
                           }},
                y->v());
          },
          [](const typename Positive::XH _args) -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsNeg_();
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return add(y, Positive::ctor::XO_(mul(std::move(p), y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XO_(mul(std::move(p), std::move(y)));
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args) -> Comparison {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return compare_cont(r, std::move(p), std::move(q));
                    },
                    [&](const typename Positive::XO _args) -> Comparison {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return compare_cont(Comparison::e_GT, std::move(p),
                                          std::move(q));
                    },
                    [](const typename Positive::XH _args) -> Comparison {
                      return Comparison::e_GT;
                    }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> Comparison {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::XI _args) -> Comparison {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return compare_cont(Comparison::e_LT, std::move(p),
                                          std::move(q));
                    },
                    [&](const typename Positive::XO _args) -> Comparison {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return compare_cont(r, std::move(p), std::move(q));
                    },
                    [](const typename Positive::XH _args) -> Comparison {
                      return Comparison::e_GT;
                    }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [](const typename Positive::XO _args) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [&](const typename Positive::XH _args)
                               -> Comparison { return r; }},
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XO_(succ(std::move(p)));
          },
          [](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XI_(std::move(p));
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(succ(std::move(q)));
                           },
                           [](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(std::move(q));
                           },
                           [](const typename Positive::XH _args)
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::XI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XI_(succ(std::move(q)));
                           },
                           [](const typename Positive::XO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return Positive::ctor::XO_(succ(std::move(q)));
                           },
                           [](const typename Positive::XH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::XI_(Positive::ctor::XH_());
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return add(y, Positive::ctor::XO_(mul(std::move(p), y)));
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return Positive::ctor::XO_(mul(std::move(p), std::move(y)));
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
  return [&](void) {
    if (n.use_count() == 1 && n->v().index() == 0) {
      auto &_rf = std::get<0>(n->v_mut());
      return n;
    } else {
      return std::visit(
          Overloaded{
              [](const typename N::N0 _args) -> std::shared_ptr<N> {
                return N::ctor::N0_();
              },
              [&](const typename N::Npos _args) -> std::shared_ptr<N> {
                std::shared_ptr<Positive> n_ = _args.d_a0;
                return std::visit(
                    Overloaded{
                        [&](const typename N::N0 _args) -> std::shared_ptr<N> {
                          return std::move(n);
                        },
                        [&](const typename N::Npos _args)
                            -> std::shared_ptr<N> {
                          std::shared_ptr<Positive> m_ = _args.d_a0;
                          return std::visit(
                              Overloaded{
                                  [](const typename Pos::mask::IsNul _args)
                                      -> std::shared_ptr<N> {
                                    return N::ctor::N0_();
                                  },
                                  [](const typename Pos::mask::IsPos _args)
                                      -> std::shared_ptr<N> {
                                    std::shared_ptr<Positive> p = _args.d_a0;
                                    return N::ctor::Npos_(std::move(p));
                                  },
                                  [](const typename Pos::mask::IsNeg _args)
                                      -> std::shared_ptr<N> {
                                    return N::ctor::N0_();
                                  }},
                              Pos::sub_mask(std::move(n_), std::move(m_))->v());
                        }},
                    m->v());
              }},
          n->v());
    }
  }();
}

__attribute__((pure)) Comparison BinNat::compare(const std::shared_ptr<N> &n,
                                                 const std::shared_ptr<N> &m) {
  return std::visit(
      Overloaded{
          [&](const typename N::N0 _args) -> Comparison {
            return std::visit(
                Overloaded{[](const typename N::N0 _args) -> Comparison {
                             return Comparison::e_EQ;
                           },
                           [](const typename N::Npos _args) -> Comparison {
                             return Comparison::e_LT;
                           }},
                m->v());
          },
          [&](const typename N::Npos _args) -> Comparison {
            std::shared_ptr<Positive> n_ = _args.d_a0;
            return std::visit(
                Overloaded{[](const typename N::N0 _args) -> Comparison {
                             return Comparison::e_GT;
                           },
                           [&](const typename N::Npos _args) -> Comparison {
                             std::shared_ptr<Positive> m_ = _args.d_a0;
                             return Pos::compare(std::move(n_), std::move(m_));
                           }},
                m->v());
          }},
      n->v());
}

std::shared_ptr<N> BinNat::pred(const std::shared_ptr<N> &n) {
  return std::visit(
      Overloaded{[](const typename N::N0 _args) -> std::shared_ptr<N> {
                   return N::ctor::N0_();
                 },
                 [](const typename N::Npos _args) -> std::shared_ptr<N> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Pos::pred_N(std::move(p));
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return [&](void) {
              if (std::move(m).use_count() == 1 &&
                  std::move(m)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(m)->v_mut());
                std::shared_ptr<Positive> q = std::move(_rf.d_a0);
                _rf.d_a0 = Coq_Pos::add(std::move(p), std::move(q));
                return std::move(m);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename N::N0 _args) -> std::shared_ptr<N> {
                          return std::move(n);
                        },
                        [&](const typename N::Npos _args)
                            -> std::shared_ptr<N> {
                          std::shared_ptr<Positive> q = _args.d_a0;
                          return N::ctor::Npos_(
                              Coq_Pos::add(std::move(p), std::move(q)));
                        }},
                    std::move(m)->v());
              }
            }();
          }},
      n->v());
}

std::shared_ptr<N> BinNat::mul(const std::shared_ptr<N> &n,
                               const std::shared_ptr<N> &m) {
  return std::visit(
      Overloaded{
          [](const typename N::N0 _args) -> std::shared_ptr<N> {
            return N::ctor::N0_();
          },
          [&](const typename N::Npos _args) -> std::shared_ptr<N> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename N::N0 _args) -> std::shared_ptr<N> {
                      return N::ctor::N0_();
                    },
                    [&](const typename N::Npos _args) -> std::shared_ptr<N> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return N::ctor::Npos_(
                          Coq_Pos::mul(std::move(p), std::move(q)));
                    }},
                m->v());
          }},
      n->v());
}

__attribute__((pure)) unsigned int BinNat::to_nat(const std::shared_ptr<N> &a) {
  return std::visit(
      Overloaded{[](const typename N::N0 _args) -> unsigned int { return 0u; },
                 [](const typename N::Npos _args) -> unsigned int {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Pos::to_nat(std::move(p));
                 }},
      a->v());
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zpos_(Positive::ctor::XO_(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zneg_(Positive::ctor::XO_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::XH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zpos_(Positive::ctor::XI_(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zneg_(Pos::pred_double(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::XH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zpos_(Pos::pred_double(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zneg_(Positive::ctor::XI_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::XI _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return BinInt::double_(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return BinInt::succ_double(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Z> {
                             return Z::ctor::Zpos_(
                                 Positive::ctor::XO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XO _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> p = _args.d_a0;
            return std::visit(
                Overloaded{[&](const typename Positive::XI _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return BinInt::pred_double(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XO _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args.d_a0;
                             return BinInt::double_(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::XH _args)
                               -> std::shared_ptr<Z> {
                             return Z::ctor::Zpos_(
                                 Pos::pred_double(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::XH _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::XI _args)
                        -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return Z::ctor::Zneg_(Positive::ctor::XO_(std::move(q)));
                    },
                    [](const typename Positive::XO _args)
                        -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> q = _args.d_a0;
                      return Z::ctor::Zneg_(Pos::pred_double(std::move(q)));
                    },
                    [](const typename Positive::XH _args)
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
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
                _rf.d_a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args.d_a0;
                          return Z::ctor::Zpos_(
                              Pos::add(std::move(x_), std::move(y_)));
                        },
                        [&](const typename Z::Zneg _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args.d_a0;
                          return BinInt::pos_sub(std::move(x_), std::move(y_));
                        }},
                    std::move(y)->v());
              }
            }();
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 2) {
                auto &_rf = std::get<2>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
                _rf.d_a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args.d_a0;
                          return BinInt::pos_sub(std::move(y_), std::move(x_));
                        },
                        [&](const typename Z::Zneg _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args.d_a0;
                          return Z::ctor::Zneg_(
                              Pos::add(std::move(x_), std::move(y_)));
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
                   std::shared_ptr<Positive> x0 = _args.d_a0;
                   return Z::ctor::Zneg_(std::move(x0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> x0 = _args.d_a0;
                   return Z::ctor::Zpos_(std::move(x0));
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
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args.d_a0;
                      return Z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args.d_a0;
                      return Z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args.d_a0;
                      return Z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args.d_a0;
                      return Z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
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
                Overloaded{[](const typename Z::Z0 _args) -> Comparison {
                             return Comparison::e_EQ;
                           },
                           [](const typename Z::Zpos _args) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [](const typename Z::Zneg _args) -> Comparison {
                             return Comparison::e_GT;
                           }},
                y->v());
          },
          [&](const typename Z::Zpos _args) -> Comparison {
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args) -> Comparison {
                             return Comparison::e_GT;
                           },
                           [&](const typename Z::Zpos _args) -> Comparison {
                             std::shared_ptr<Positive> y_ = _args.d_a0;
                             return Pos::compare(std::move(x_), std::move(y_));
                           },
                           [](const typename Z::Zneg _args) -> Comparison {
                             return Comparison::e_GT;
                           }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> Comparison {
            std::shared_ptr<Positive> x_ = _args.d_a0;
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [](const typename Z::Zpos _args) -> Comparison {
                             return Comparison::e_LT;
                           },
                           [&](const typename Z::Zneg _args) -> Comparison {
                             std::shared_ptr<Positive> y_ = _args.d_a0;
                             return Datatypes::CompOpp(
                                 Pos::compare(std::move(x_), std::move(y_)));
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
            std::shared_ptr<Positive> p = _args.d_a0;
            return Pos::to_nat(std::move(p));
          },
          [](const typename Z::Zneg _args) -> unsigned int { return 0u; }},
      z->v());
}

std::shared_ptr<Z> BinInt::abs(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Z0_();
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zpos_(std::move(p));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args.d_a0;
                   return Z::ctor::Zpos_(std::move(p));
                 }},
      z->v());
}

std::shared_ptr<N> BinaryNums::n_max(std::shared_ptr<N> a,
                                     std::shared_ptr<N> b) {
  return [&](void) {
    switch (BinNat::compare(a, b)) {
    case Comparison::e_EQ: {
      return std::move(a);
    }
    case Comparison::e_LT: {
      return std::move(b);
    }
    case Comparison::e_GT: {
      return std::move(a);
    }
    }
  }();
}

std::shared_ptr<Z> BinaryNums::z_sign(const std::shared_ptr<Z> &z) {
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
