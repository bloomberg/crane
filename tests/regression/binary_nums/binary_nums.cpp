#include <algorithm>
#include <any>
#include <binary_nums.h>
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
          [](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xO_(succ(std::move(p)));
          },
          [](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xI_(std::move(p));
          },
          [](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::xO_(Positive::ctor::xH_());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(succ(std::move(q)));
                           },
                           [](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(std::move(q));
                           },
                           [](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(Positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::add_carry(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(succ(std::move(q)));
                           },
                           [](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(succ(std::move(q)));
                           },
                           [](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(Positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xI_(Positive::ctor::xO_(std::move(p)));
          },
          [](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xI_(pred_double(std::move(p)));
          },
          [](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::xH_();
          }},
      x->v());
}

std::shared_ptr<N> Pos::pred_N(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::xI _args) -> std::shared_ptr<N> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return N::ctor::Npos_(Positive::ctor::xO_(std::move(p)));
                 },
                 [](const typename Positive::xO _args) -> std::shared_ptr<N> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return N::ctor::Npos_(pred_double(std::move(p)));
                 },
                 [](const typename Positive::xH _args) -> std::shared_ptr<N> {
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
            return mask::ctor::IsPos_(Positive::ctor::xH_());
          },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return mask::ctor::IsPos_(Positive::ctor::xI_(std::move(p)));
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
            std::shared_ptr<Positive> p = _args._a0;
            return mask::ctor::IsPos_(Positive::ctor::xO_(std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::xI _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return mask::ctor::IsPos_(
                Positive::ctor::xO_(Positive::ctor::xO_(std::move(p))));
          },
          [](const typename Positive::xO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return mask::ctor::IsPos_(
                Positive::ctor::xO_(pred_double(std::move(p))));
          },
          [](const typename Positive::xH _args) -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsNul_();
          }},
      x->v());
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return succ_double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsPos_(
                                 Positive::ctor::xO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::xI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::xO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::xH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Pos::mask> {
            return std::visit(Overloaded{[](const typename Positive::xI _args)
                                             -> std::shared_ptr<Pos::mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::xO _args)
                                             -> std::shared_ptr<Pos::mask> {
                                           return mask::ctor::IsNeg_();
                                         },
                                         [](const typename Positive::xH _args)
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
          [&](const typename Positive::xI _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::xI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::xO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::xH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return succ_double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return double_pred_mask(std::move(p));
                           }},
                y->v());
          },
          [](const typename Positive::xH _args) -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsNeg_();
          }},
      x->v());
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return add(y, Positive::ctor::xO_(mul(std::move(p), y)));
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xO_(mul(std::move(p), std::move(y)));
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::move(y);
          }},
      x->v());
}

comparison Pos::compare_cont(const comparison r,
                             const std::shared_ptr<Positive> &x,
                             const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> comparison {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::xI _args) -> comparison {
                      std::shared_ptr<Positive> q = _args._a0;
                      return compare_cont(r, std::move(p), std::move(q));
                    },
                    [&](const typename Positive::xO _args) -> comparison {
                      std::shared_ptr<Positive> q = _args._a0;
                      return compare_cont(comparison::Gt, std::move(p),
                                          std::move(q));
                    },
                    [](const typename Positive::xH _args) -> comparison {
                      return comparison::Gt;
                    }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> comparison {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::xI _args) -> comparison {
                      std::shared_ptr<Positive> q = _args._a0;
                      return compare_cont(comparison::Lt, std::move(p),
                                          std::move(q));
                    },
                    [&](const typename Positive::xO _args) -> comparison {
                      std::shared_ptr<Positive> q = _args._a0;
                      return compare_cont(r, std::move(p), std::move(q));
                    },
                    [](const typename Positive::xH _args) -> comparison {
                      return comparison::Gt;
                    }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename Positive::xI _args) -> comparison {
                             return comparison::Lt;
                           },
                           [](const typename Positive::xO _args) -> comparison {
                             return comparison::Lt;
                           },
                           [&](const typename Positive::xH _args)
                               -> comparison { return r; }},
                y->v());
          }},
      x->v());
}

comparison Pos::compare(const std::shared_ptr<Positive> &_x0,
                        const std::shared_ptr<Positive> &_x1) {
  return compare_cont(comparison::Eq, _x0, _x1);
}

unsigned int Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<Positive> Coq_Pos::succ(const std::shared_ptr<Positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xO_(succ(std::move(p)));
          },
          [](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xI_(std::move(p));
          },
          [](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return Positive::ctor::xO_(Positive::ctor::xH_());
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(succ(std::move(q)));
                           },
                           [](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(std::move(q));
                           },
                           [](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(Positive::ctor::xH_());
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
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xO_(succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::visit(
                Overloaded{[](const typename Positive::xI _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xI_(succ(std::move(q)));
                           },
                           [](const typename Positive::xO _args)
                               -> std::shared_ptr<Positive> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return Positive::ctor::xO_(succ(std::move(q)));
                           },
                           [](const typename Positive::xH _args)
                               -> std::shared_ptr<Positive> {
                             return Positive::ctor::xI_(Positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive> Coq_Pos::mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return add(y, Positive::ctor::xO_(mul(std::move(p), y)));
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Positive> {
            std::shared_ptr<Positive> p = _args._a0;
            return Positive::ctor::xO_(mul(std::move(p), std::move(y)));
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Positive> {
            return std::move(y);
          }},
      x->v());
}

unsigned int Coq_Pos::to_nat(const std::shared_ptr<Positive> &x) {
  return iter_op<unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      x, 1u);
}

std::shared_ptr<N> BinNat::sub(std::shared_ptr<N> n,
                               const std::shared_ptr<N> &m) {
  return [&](void) {
    if (((n.use_count() == 1) && (n->v().index() == 0))) {
      auto &_rf = std::get<0>(n->v_mut());
      return n;
    } else {
      return std::visit(
          Overloaded{
              [](const typename N::N0 _args) -> std::shared_ptr<N> {
                return N::ctor::N0_();
              },
              [&](const typename N::Npos _args) -> std::shared_ptr<N> {
                std::shared_ptr<Positive> n_ = _args._a0;
                return std::visit(
                    Overloaded{
                        [&](const typename N::N0 _args) -> std::shared_ptr<N> {
                          return std::move(n);
                        },
                        [&](const typename N::Npos _args)
                            -> std::shared_ptr<N> {
                          std::shared_ptr<Positive> m_ = _args._a0;
                          return std::visit(
                              Overloaded{
                                  [](const typename Pos::mask::IsNul _args)
                                      -> std::shared_ptr<N> {
                                    return N::ctor::N0_();
                                  },
                                  [](const typename Pos::mask::IsPos _args)
                                      -> std::shared_ptr<N> {
                                    std::shared_ptr<Positive> p = _args._a0;
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

comparison BinNat::compare(const std::shared_ptr<N> &n,
                           const std::shared_ptr<N> &m) {
  return std::visit(
      Overloaded{
          [&](const typename N::N0 _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename N::N0 _args) -> comparison {
                             return comparison::Eq;
                           },
                           [](const typename N::Npos _args) -> comparison {
                             return comparison::Lt;
                           }},
                m->v());
          },
          [&](const typename N::Npos _args) -> comparison {
            std::shared_ptr<Positive> n_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename N::N0 _args) -> comparison {
                             return comparison::Gt;
                           },
                           [&](const typename N::Npos _args) -> comparison {
                             std::shared_ptr<Positive> m_ = _args._a0;
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
                   std::shared_ptr<Positive> p = _args._a0;
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
            std::shared_ptr<Positive> p = _args._a0;
            return [&](void) {
              if (((std::move(m).use_count() == 1) &&
                   (std::move(m)->v().index() == 1))) {
                auto &_rf = std::get<1>(std::move(m)->v_mut());
                std::shared_ptr<Positive> q = std::move(_rf._a0);
                _rf._a0 = Coq_Pos::add(std::move(p), std::move(q));
                return std::move(m);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename N::N0 _args) -> std::shared_ptr<N> {
                          return std::move(n);
                        },
                        [&](const typename N::Npos _args)
                            -> std::shared_ptr<N> {
                          std::shared_ptr<Positive> q = _args._a0;
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
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename N::N0 _args) -> std::shared_ptr<N> {
                      return N::ctor::N0_();
                    },
                    [&](const typename N::Npos _args) -> std::shared_ptr<N> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return N::ctor::Npos_(
                          Coq_Pos::mul(std::move(p), std::move(q)));
                    }},
                m->v());
          }},
      n->v());
}

unsigned int BinNat::to_nat(const std::shared_ptr<N> &a) {
  return std::visit(
      Overloaded{[](const typename N::N0 _args) -> unsigned int { return 0u; },
                 [](const typename N::Npos _args) -> unsigned int {
                   std::shared_ptr<Positive> p = _args._a0;
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
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zpos_(Positive::ctor::xO_(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zneg_(Positive::ctor::xO_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zpos_(Positive::ctor::xH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zpos_(Positive::ctor::xI_(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zneg_(Pos::pred_double(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::xH_());
                 },
                 [](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zpos_(Pos::pred_double(std::move(p)));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zneg_(Positive::ctor::xI_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::xI _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return BinInt::double_(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return BinInt::succ_double(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Z> {
                             return Z::ctor::Zpos_(
                                 Positive::ctor::xO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xO _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::xI _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return BinInt::pred_double(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xO _args)
                               -> std::shared_ptr<Z> {
                             std::shared_ptr<Positive> q = _args._a0;
                             return BinInt::double_(
                                 BinInt::pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::xH _args)
                               -> std::shared_ptr<Z> {
                             return Z::ctor::Zpos_(
                                 Pos::pred_double(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::xH _args) -> std::shared_ptr<Z> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::xI _args)
                        -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return Z::ctor::Zneg_(Positive::ctor::xO_(std::move(q)));
                    },
                    [](const typename Positive::xO _args)
                        -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> q = _args._a0;
                      return Z::ctor::Zneg_(Pos::pred_double(std::move(q)));
                    },
                    [](const typename Positive::xH _args)
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
            std::shared_ptr<Positive> x_ = _args._a0;
            return [&](void) {
              if (((std::move(y).use_count() == 1) &&
                   (std::move(y)->v().index() == 1))) {
                auto &_rf = std::get<1>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf._a0);
                _rf._a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args._a0;
                          return Z::ctor::Zpos_(
                              Pos::add(std::move(x_), std::move(y_)));
                        },
                        [&](const typename Z::Zneg _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args._a0;
                          return BinInt::pos_sub(std::move(x_), std::move(y_));
                        }},
                    std::move(y)->v());
              }
            }();
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> x_ = _args._a0;
            return [&](void) {
              if (((std::move(y).use_count() == 1) &&
                   (std::move(y)->v().index() == 2))) {
                auto &_rf = std::get<2>(std::move(y)->v_mut());
                std::shared_ptr<Positive> y_ = std::move(_rf._a0);
                _rf._a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                          return std::move(x);
                        },
                        [&](const typename Z::Zpos _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args._a0;
                          return BinInt::pos_sub(std::move(y_), std::move(x_));
                        },
                        [&](const typename Z::Zneg _args)
                            -> std::shared_ptr<Z> {
                          std::shared_ptr<Positive> y_ = _args._a0;
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
                   std::shared_ptr<Positive> x0 = _args._a0;
                   return Z::ctor::Zneg_(std::move(x0));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> x0 = _args._a0;
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
            std::shared_ptr<Positive> x_ = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args._a0;
                      return Z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args._a0;
                      return Z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
            std::shared_ptr<Positive> x_ = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::Z0 _args) -> std::shared_ptr<Z> {
                      return Z::ctor::Z0_();
                    },
                    [&](const typename Z::Zpos _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args._a0;
                      return Z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                      std::shared_ptr<Positive> y_ = _args._a0;
                      return Z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    }},
                y->v());
          }},
      x->v());
}

comparison BinInt::compare(const std::shared_ptr<Z> &x,
                           const std::shared_ptr<Z> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::Z0 _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args) -> comparison {
                             return comparison::Eq;
                           },
                           [](const typename Z::Zpos _args) -> comparison {
                             return comparison::Lt;
                           },
                           [](const typename Z::Zneg _args) -> comparison {
                             return comparison::Gt;
                           }},
                y->v());
          },
          [&](const typename Z::Zpos _args) -> comparison {
            std::shared_ptr<Positive> x_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args) -> comparison {
                             return comparison::Gt;
                           },
                           [&](const typename Z::Zpos _args) -> comparison {
                             std::shared_ptr<Positive> y_ = _args._a0;
                             return Pos::compare(std::move(x_), std::move(y_));
                           },
                           [](const typename Z::Zneg _args) -> comparison {
                             return comparison::Gt;
                           }},
                y->v());
          },
          [&](const typename Z::Zneg _args) -> comparison {
            std::shared_ptr<Positive> x_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename Z::Z0 _args) -> comparison {
                             return comparison::Lt;
                           },
                           [](const typename Z::Zpos _args) -> comparison {
                             return comparison::Lt;
                           },
                           [&](const typename Z::Zneg _args) -> comparison {
                             std::shared_ptr<Positive> y_ = _args._a0;
                             return Datatypes::CompOpp(
                                 Pos::compare(std::move(x_), std::move(y_)));
                           }},
                y->v());
          }},
      x->v());
}

unsigned int BinInt::to_nat(const std::shared_ptr<Z> &z) {
  return std::visit(
      Overloaded{
          [](const typename Z::Z0 _args) -> unsigned int { return 0u; },
          [](const typename Z::Zpos _args) -> unsigned int {
            std::shared_ptr<Positive> p = _args._a0;
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
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zpos_(std::move(p));
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   std::shared_ptr<Positive> p = _args._a0;
                   return Z::ctor::Zpos_(std::move(p));
                 }},
      z->v());
}

std::shared_ptr<N> BinaryNums::n_max(std::shared_ptr<N> a,
                                     std::shared_ptr<N> b) {
  return [&](void) {
    switch (BinNat::compare(a, b)) {
    case comparison::Eq: {
      return std::move(a);
    }
    case comparison::Lt: {
      return std::move(b);
    }
    case comparison::Gt: {
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
                   return Z::ctor::Zpos_(Positive::ctor::xH_());
                 },
                 [](const typename Z::Zneg _args) -> std::shared_ptr<Z> {
                   return Z::ctor::Zneg_(Positive::ctor::xH_());
                 }},
      z->v());
}

comparison Datatypes::CompOpp(const comparison r) {
  return [&](void) {
    switch (r) {
    case comparison::Eq: {
      return comparison::Eq;
    }
    case comparison::Lt: {
      return comparison::Gt;
    }
    case comparison::Gt: {
      return comparison::Lt;
    }
    }
  }();
}
