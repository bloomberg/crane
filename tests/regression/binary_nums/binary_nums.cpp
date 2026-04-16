#include <binary_nums.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<Positive> Pos::succ(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return Positive::xo(succ(d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return Positive::xi(d_a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

std::shared_ptr<Positive> Pos::add(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else {
      return Positive::xo(succ(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(add(d_a0, d_a00));
    } else {
      return Positive::xi(d_a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(succ(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(d_a00);
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

std::shared_ptr<Positive> Pos::add_carry(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else {
      return Positive::xi(succ(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else {
      return Positive::xo(succ(d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(succ(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(succ(d_a00));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

std::shared_ptr<Positive> Pos::pred_double(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return Positive::xi(Positive::xo(d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return Positive::xi(pred_double(d_a0));
  } else {
    return Positive::xh();
  }
}

std::shared_ptr<N> Pos::pred_N(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return N::npos(Positive::xo(d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return N::npos(pred_double(d_a0));
  } else {
    return N::n0();
  }
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x->v())) {
    return mask::ispos(Positive::xh());
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x->v())) {
    const auto &[d_a0] = std::get<typename Pos::mask::IsPos>(x->v());
    return mask::ispos(Positive::xi(d_a0));
  } else {
    return mask::isneg();
  }
}

std::shared_ptr<Pos::mask>
Pos::double_mask(const std::shared_ptr<Pos::mask> &x) {
  if (std::holds_alternative<typename Pos::mask::IsNul>(x->v())) {
    return mask::isnul();
  } else if (std::holds_alternative<typename Pos::mask::IsPos>(x->v())) {
    const auto &[d_a0] = std::get<typename Pos::mask::IsPos>(x->v());
    return mask::ispos(Positive::xo(d_a0));
  } else {
    return mask::isneg();
  }
}

std::shared_ptr<Pos::mask>
Pos::double_pred_mask(const std::shared_ptr<Positive> &x) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return mask::ispos(Positive::xo(Positive::xo(d_a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return mask::ispos(Positive::xo(pred_double(d_a0)));
  } else {
    return mask::isnul();
  }
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const std::shared_ptr<Positive> &x,
                                         const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return double_mask(sub_mask(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return succ_double_mask(sub_mask(d_a0, d_a00));
    } else {
      return mask::ispos(Positive::xo(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return succ_double_mask(sub_mask_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return double_mask(sub_mask(d_a0, d_a00));
    } else {
      return mask::ispos(pred_double(d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y->v())) {
      return mask::isnul();
    } else {
      return mask::isneg();
    }
  }
}

std::shared_ptr<Pos::mask>
Pos::sub_mask_carry(const std::shared_ptr<Positive> &x,
                    const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return succ_double_mask(sub_mask_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return double_mask(sub_mask(d_a0, d_a00));
    } else {
      return mask::ispos(pred_double(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return double_mask(sub_mask_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return succ_double_mask(sub_mask_carry(d_a0, d_a00));
    } else {
      return double_pred_mask(d_a0);
    }
  } else {
    return mask::isneg();
  }
}

std::shared_ptr<Positive> Pos::mul(const std::shared_ptr<Positive> &x,
                                   std::shared_ptr<Positive> y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return add(y, Positive::xo(mul(d_a0, y)));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return Positive::xo(mul(d_a0, y));
  } else {
    return y;
  }
}

__attribute__((pure)) Comparison
Pos::compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
                  const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return compare_cont(r, d_a0, d_a00);
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return compare_cont(Comparison::e_GT, d_a0, d_a00);
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return compare_cont(Comparison::e_LT, d_a0, d_a00);
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return compare_cont(r, d_a0, d_a00);
    } else {
      return Comparison::e_GT;
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y->v())) {
      return r;
    } else {
      return Comparison::e_LT;
    }
  }
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
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return Positive::xo(succ(d_a0));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return Positive::xi(d_a0);
  } else {
    return Positive::xo(Positive::xh());
  }
}

std::shared_ptr<Positive> Coq_Pos::add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else {
      return Positive::xo(succ(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(add(d_a0, d_a00));
    } else {
      return Positive::xi(d_a0);
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(succ(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(d_a00);
    } else {
      return Positive::xo(Positive::xh());
    }
  }
}

std::shared_ptr<Positive>
Coq_Pos::add_carry(const std::shared_ptr<Positive> &x,
                   const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else {
      return Positive::xi(succ(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xo(add_carry(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xi(add(d_a0, d_a00));
    } else {
      return Positive::xo(succ(d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Positive::xi(succ(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Positive::xo(succ(d_a00));
    } else {
      return Positive::xi(Positive::xh());
    }
  }
}

std::shared_ptr<Positive> Coq_Pos::mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    return add(y, Positive::xo(mul(d_a0, y)));
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    return Positive::xo(mul(d_a0, y));
  } else {
    return y;
  }
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
  if (std::holds_alternative<typename N::N0>(n->v())) {
    return N::n0();
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(n->v());
    if (std::holds_alternative<typename N::N0>(m->v())) {
      return n;
    } else {
      const auto &[d_a00] = std::get<typename N::Npos>(m->v());
      auto &&_sv1 = Pos::sub_mask(d_a0, d_a00);
      if (std::holds_alternative<typename Pos::mask::IsPos>(_sv1->v())) {
        const auto &[d_a01] = std::get<typename Pos::mask::IsPos>(_sv1->v());
        return N::npos(d_a01);
      } else {
        return N::n0();
      }
    }
  }
}

__attribute__((pure)) Comparison BinNat::compare(const std::shared_ptr<N> &n,
                                                 const std::shared_ptr<N> &m) {
  if (std::holds_alternative<typename N::N0>(n->v())) {
    if (std::holds_alternative<typename N::N0>(m->v())) {
      return Comparison::e_EQ;
    } else {
      return Comparison::e_LT;
    }
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(n->v());
    if (std::holds_alternative<typename N::N0>(m->v())) {
      return Comparison::e_GT;
    } else {
      const auto &[d_a00] = std::get<typename N::Npos>(m->v());
      return Pos::compare(d_a0, d_a00);
    }
  }
}

std::shared_ptr<N> BinNat::pred(const std::shared_ptr<N> &n) {
  if (std::holds_alternative<typename N::N0>(n->v())) {
    return N::n0();
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(n->v());
    return Pos::pred_N(d_a0);
  }
}

std::shared_ptr<N> BinNat::add(std::shared_ptr<N> n, std::shared_ptr<N> m) {
  if (std::holds_alternative<typename N::N0>(n->v())) {
    return m;
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(n->v());
    if (std::holds_alternative<typename N::N0>(m->v())) {
      return n;
    } else {
      if (m.use_count() == 1) {
        auto &_rf = std::get<typename N::Npos>(m->v_mut());
        std::shared_ptr<Positive> q = std::move(_rf.d_a0);
        _rf.d_a0 = Coq_Pos::add(std::move(d_a0), q);
        return m;
      } else {
        const auto &[d_a00] = std::get<typename N::Npos>(m->v());
        return N::npos(Coq_Pos::add(d_a0, d_a00));
      }
    }
  }
}

std::shared_ptr<N> BinNat::mul(const std::shared_ptr<N> &n,
                               const std::shared_ptr<N> &m) {
  if (std::holds_alternative<typename N::N0>(n->v())) {
    return N::n0();
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(n->v());
    if (std::holds_alternative<typename N::N0>(m->v())) {
      return N::n0();
    } else {
      const auto &[d_a00] = std::get<typename N::Npos>(m->v());
      return N::npos(Coq_Pos::mul(d_a0, d_a00));
    }
  }
}

__attribute__((pure)) unsigned int BinNat::to_nat(const std::shared_ptr<N> &a) {
  if (std::holds_alternative<typename N::N0>(a->v())) {
    return 0u;
  } else {
    const auto &[d_a0] = std::get<typename N::Npos>(a->v());
    return Pos::to_nat(d_a0);
  }
}

std::shared_ptr<Z> BinInt::double_(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    return Z::zpos(Positive::xo(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    return Z::zneg(Positive::xo(d_a0));
  }
}

std::shared_ptr<Z> BinInt::succ_double(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    return Z::zpos(Positive::xi(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    return Z::zneg(Pos::pred_double(d_a0));
  }
}

std::shared_ptr<Z> BinInt::pred_double(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::zneg(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    return Z::zpos(Pos::pred_double(d_a0));
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    return Z::zneg(Positive::xi(d_a0));
  }
}

std::shared_ptr<Z> BinInt::pos_sub(const std::shared_ptr<Positive> &x,
                                   const std::shared_ptr<Positive> &y) {
  if (std::holds_alternative<typename Positive::XI>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XI>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return BinInt::double_(BinInt::pos_sub(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return BinInt::succ_double(BinInt::pos_sub(d_a0, d_a00));
    } else {
      return Z::zpos(Positive::xo(d_a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x->v())) {
    const auto &[d_a0] = std::get<typename Positive::XO>(x->v());
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return BinInt::pred_double(BinInt::pos_sub(d_a0, d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return BinInt::double_(BinInt::pos_sub(d_a0, d_a00));
    } else {
      return Z::zpos(Pos::pred_double(d_a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XI>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XI>(y->v());
      return Z::zneg(Positive::xo(d_a00));
    } else if (std::holds_alternative<typename Positive::XO>(y->v())) {
      const auto &[d_a00] = std::get<typename Positive::XO>(y->v());
      return Z::zneg(Pos::pred_double(d_a00));
    } else {
      return Z::z0();
    }
  }
}

std::shared_ptr<Z> BinInt::add(std::shared_ptr<Z> x, std::shared_ptr<Z> y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      if (y.use_count() == 1) {
        auto &_rf = std::get<typename Z::Zpos>(y->v_mut());
        std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
        _rf.d_a0 = Pos::add(std::move(d_a0), y_);
        return y;
      } else {
        const auto &[d_a00] = std::get<typename Z::Zpos>(y->v());
        return Z::zpos(Pos::add(d_a0, d_a00));
      }

    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y->v());
      return BinInt::pos_sub(d_a0, d_a00);
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y->v());
      return BinInt::pos_sub(d_a00, d_a0);
    } else {
      if (y.use_count() == 1) {
        auto &_rf = std::get<typename Z::Zneg>(y->v_mut());
        std::shared_ptr<Positive> y_ = std::move(_rf.d_a0);
        _rf.d_a0 = Pos::add(std::move(d_a0), y_);
        return y;
      } else {
        const auto &[d_a00] = std::get<typename Z::Zneg>(y->v());
        return Z::zneg(Pos::add(d_a0, d_a00));
      }
    }
  }
}

std::shared_ptr<Z> BinInt::opp(const std::shared_ptr<Z> &x) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    return Z::zneg(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    return Z::zpos(d_a0);
  }
}

std::shared_ptr<Z> BinInt::sub(const std::shared_ptr<Z> &m,
                               const std::shared_ptr<Z> &n) {
  return BinInt::add(m, BinInt::opp(n));
}

std::shared_ptr<Z> BinInt::mul(const std::shared_ptr<Z> &x,
                               const std::shared_ptr<Z> &y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y->v());
      return Z::zpos(Pos::mul(d_a0, d_a00));
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y->v());
      return Z::zneg(Pos::mul(d_a0, d_a00));
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y->v());
      return Z::zneg(Pos::mul(d_a0, d_a00));
    } else {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y->v());
      return Z::zpos(Pos::mul(d_a0, d_a00));
    }
  }
}

__attribute__((pure)) Comparison BinInt::compare(const std::shared_ptr<Z> &x,
                                                 const std::shared_ptr<Z> &y) {
  if (std::holds_alternative<typename Z::Z0>(x->v())) {
    if (std::holds_alternative<typename Z::Z0>(y->v())) {
      return Comparison::e_EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      return Comparison::e_LT;
    } else {
      return Comparison::e_GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(x->v());
    if (std::holds_alternative<typename Z::Zpos>(y->v())) {
      const auto &[d_a00] = std::get<typename Z::Zpos>(y->v());
      return Pos::compare(d_a0, d_a00);
    } else {
      return Comparison::e_GT;
    }
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(x->v());
    if (std::holds_alternative<typename Z::Zneg>(y->v())) {
      const auto &[d_a00] = std::get<typename Z::Zneg>(y->v());
      return Datatypes::CompOpp(Pos::compare(d_a0, d_a00));
    } else {
      return Comparison::e_LT;
    }
  }
}

__attribute__((pure)) unsigned int BinInt::to_nat(const std::shared_ptr<Z> &z) {
  if (std::holds_alternative<typename Z::Zpos>(z->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(z->v());
    return Pos::to_nat(d_a0);
  } else {
    return 0u;
  }
}

std::shared_ptr<Z> BinInt::abs(const std::shared_ptr<Z> &z) {
  if (std::holds_alternative<typename Z::Z0>(z->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z->v())) {
    const auto &[d_a0] = std::get<typename Z::Zpos>(z->v());
    return Z::zpos(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Z::Zneg>(z->v());
    return Z::zpos(d_a0);
  }
}

std::shared_ptr<N> BinaryNums::n_max(std::shared_ptr<N> a,
                                     std::shared_ptr<N> b) {
  switch (BinNat::compare(a, b)) {
  case Comparison::e_LT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

std::shared_ptr<Z> BinaryNums::z_sign(const std::shared_ptr<Z> &z) {
  if (std::holds_alternative<typename Z::Z0>(z->v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(z->v())) {
    return Z::zpos(Positive::xh());
  } else {
    return Z::zneg(Positive::xh());
  }
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
