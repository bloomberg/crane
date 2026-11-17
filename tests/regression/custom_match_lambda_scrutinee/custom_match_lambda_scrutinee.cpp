#include "custom_match_lambda_scrutinee.h"

bool CustomMatchLambdaScrutinee::dtyp_base_eq_dec(
    const CustomMatchLambdaScrutinee::dtyp_base &t1,
    const CustomMatchLambdaScrutinee::dtyp_base &t2) {
  if (std::holds_alternative<
          typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_I>(t1.v())) {
    const auto &[sz0] =
        std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_I>(
            t1.v());
    if (std::holds_alternative<
            typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_I>(t2.v())) {
      const auto &[sz2] =
          std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_I>(
              t2.v());

      if ([&]() {
        auto f_impl =
            [](auto &_self_f, const Positive &p, const Positive &x) -> bool {
              if (std::holds_alternative<typename Positive::XI>(p.v())) {
                const auto &[a0] = std::get<typename Positive::XI>(p.v());
                if (std::holds_alternative<typename Positive::XI>(x.v())) {
                  const auto &[a00] = std::get<typename Positive::XI>(x.v());
                  if (_self_f(_self_f, *a0, *a00)) {
                    return true;
                  } else {
                    return false;
                  }
                } else {
                  return false;
                }
              } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
                const auto &[a0] = std::get<typename Positive::XO>(p.v());
                if (std::holds_alternative<typename Positive::XO>(x.v())) {
                  const auto &[a00] = std::get<typename Positive::XO>(x.v());
                  if (_self_f(_self_f, *a0, *a00)) {
                    return true;
                  } else {
                    return false;
                  }
                } else {
                  return false;
                }
              } else {
                if (std::holds_alternative<typename Positive::XH>(x.v())) {
                  return true;
                } else {
                  return false;
                }
              }
            };
        auto f =
            [&](const Positive &p,
                const Positive &x)
                 -> bool { return f_impl(f_impl, p, x); };
        return f(sz0, sz2);
      }()) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else if (
      std::holds_alternative<
          typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_Iptr>(t1.v())) {
    if (std::holds_alternative<
            typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_Iptr>(t2.v())) {
      return true;
    } else {
      return false;
    }
  } else if (
      std::holds_alternative<
          typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_FP>(t1.v())) {
    const auto &[fp0] =
        std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_FP>(
            t1.v());
    if (std::holds_alternative<
            typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_FP>(t2.v())) {
      const auto &[fp2] =
          std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_FP>(
              t2.v());
      switch (fp0) {
      case Fpv::FP_HALF: {
        switch (fp2) {
        case Fpv::FP_HALF: {
          return true;
        }
        default: {
          return false;
        }
        }
        break;
      }
      case Fpv::FP_FLOAT: {
        switch (fp2) {
        case Fpv::FP_FLOAT: {
          return true;
        }
        default: {
          return false;
        }
        }
        break;
      }
      case Fpv::FP_DOUBLE: {
        switch (fp2) {
        case Fpv::FP_DOUBLE: {
          return true;
        }
        default: {
          return false;
        }
        }
        break;
      }
      default:
        std::unreachable();
      }
    } else {
      return false;
    }
  } else {
    const auto &[sz0] =
        std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_B>(
            t1.v());
    if (std::holds_alternative<
            typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_B>(t2.v())) {
      const auto &[sz2] =
          std::get<typename CustomMatchLambdaScrutinee::dtyp_base::DTYPE_B>(
              t2.v());

      if ([&]() {
        auto f_impl =
            [](auto &_self_f, const Positive &p, const Positive &x) -> bool {
              if (std::holds_alternative<typename Positive::XI>(p.v())) {
                const auto &[a0] = std::get<typename Positive::XI>(p.v());
                if (std::holds_alternative<typename Positive::XI>(x.v())) {
                  const auto &[a00] = std::get<typename Positive::XI>(x.v());
                  if (_self_f(_self_f, *a0, *a00)) {
                    return true;
                  } else {
                    return false;
                  }
                } else {
                  return false;
                }
              } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
                const auto &[a0] = std::get<typename Positive::XO>(p.v());
                if (std::holds_alternative<typename Positive::XO>(x.v())) {
                  const auto &[a00] = std::get<typename Positive::XO>(x.v());
                  if (_self_f(_self_f, *a0, *a00)) {
                    return true;
                  } else {
                    return false;
                  }
                } else {
                  return false;
                }
              } else {
                if (std::holds_alternative<typename Positive::XH>(x.v())) {
                  return true;
                } else {
                  return false;
                }
              }
            };
        auto f =
            [&](const Positive &p,
                const Positive &x)
                 -> bool { return f_impl(f_impl, p, x); };
        return f(sz0, sz2);
      }()) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
}

bool CustomMatchLambdaScrutinee::dtyp_base_eqb(
    const CustomMatchLambdaScrutinee::dtyp_base &a,
    const CustomMatchLambdaScrutinee::dtyp_base &b) {
  if (dtyp_base_eq_dec(a, b)) {
    return true;
  } else {
    return false;
  }
}
