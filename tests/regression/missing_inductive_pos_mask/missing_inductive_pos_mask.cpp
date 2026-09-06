#include "missing_inductive_pos_mask.h"

Positive Coq_Pos::pred_double(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return Positive::xi(Positive::xo(*a0));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return Positive::xi(pred_double(*a0));
  } else {
    return Positive::xh();
  }
}

Coq_Pos::mask Coq_Pos::succ_double_mask(const Coq_Pos::mask &x) {
  if (std::holds_alternative<typename Coq_Pos::mask::IsNul>(x.v())) {
    return mask::ispos(Positive::xh());
  } else if (std::holds_alternative<typename Coq_Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Coq_Pos::mask::IsPos>(x.v());
    return mask::ispos(Positive::xi(a0));
  } else {
    return mask::isneg();
  }
}

Coq_Pos::mask Coq_Pos::double_mask(const Coq_Pos::mask &x) {
  if (std::holds_alternative<typename Coq_Pos::mask::IsNul>(x.v())) {
    return mask::isnul();
  } else if (std::holds_alternative<typename Coq_Pos::mask::IsPos>(x.v())) {
    const auto &[a0] = std::get<typename Coq_Pos::mask::IsPos>(x.v());
    return mask::ispos(Positive::xo(a0));
  } else {
    return mask::isneg();
  }
}

Coq_Pos::mask Coq_Pos::double_pred_mask(const Positive &x) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    return mask::ispos(Positive::xo(Positive::xo(*a0)));
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    return mask::ispos(Positive::xo(pred_double(*a0)));
  } else {
    return mask::isnul();
  }
}

Coq_Pos::mask Coq_Pos::sub_mask(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(Positive::xo(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else {
    if (std::holds_alternative<typename Positive::XH>(y.v())) {
      return mask::isnul();
    } else {
      return mask::isneg();
    }
  }
}

Coq_Pos::mask Coq_Pos::sub_mask_carry(const Positive &x, const Positive &y) {
  if (std::holds_alternative<typename Positive::XI>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XI>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return double_mask(sub_mask(*a0, *a00));
    } else {
      return mask::ispos(pred_double(*a0));
    }
  } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
    const auto &[a0] = std::get<typename Positive::XO>(x.v());
    if (std::holds_alternative<typename Positive::XI>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XI>(y.v());
      return double_mask(sub_mask_carry(*a0, *a00));
    } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
      const auto &[a00] = std::get<typename Positive::XO>(y.v());
      return succ_double_mask(sub_mask_carry(*a0, *a00));
    } else {
      return double_pred_mask(*a0);
    }
  } else {
    return mask::isneg();
  }
}

Coq_Pos::mask MissingInductivePosMask::f(const Positive &x0_,
                                         const Positive &x1_) {
  return Coq_Pos::sub_mask(x0_, x1_);
}
