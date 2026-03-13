#include <n_gmp.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <gmpxx.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) mpz_class Pos::succ(const mpz_class x) {
  if (x == 1) {
    return (2 * mpz_class(1));
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    return (2 * succ(p));
  } else {
    mpz_class p = x / 2;
    return (2 * p + 1);
  }
}

__attribute__((pure)) mpz_class Pos::pred_double(const mpz_class x) {
  if (x == 1) {
    return mpz_class(1);
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    return (2 * (2 * p) + 1);
  } else {
    mpz_class p = x / 2;
    return (2 * pred_double(p) + 1);
  }
}

__attribute__((pure)) mpz_class Pos::pred_N(const mpz_class x) {
  if (x == 1) {
    return mpz_class(0);
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    return (2 * p);
  } else {
    mpz_class p = x / 2;
    return pred_double(p);
  }
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsPos_(mpz_class(1));
          },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            mpz_class p = _args.d_a0;
            return mask::ctor::IsPos_((2 * std::move(p) + 1));
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
            mpz_class p = _args.d_a0;
            return mask::ctor::IsPos_((2 * std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask> Pos::double_pred_mask(const mpz_class x) {
  if (x == 1) {
    return mask::ctor::IsNul_();
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    return mask::ctor::IsPos_((2 * (2 * p)));
  } else {
    mpz_class p = x / 2;
    return mask::ctor::IsPos_((2 * pred_double(p)));
  }
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const mpz_class x, const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return mask::ctor::IsNul_();
    } else if (y % 2 != 0) {
      mpz_class _x = (y - 1) / 2;
      return mask::ctor::IsNeg_();
    } else {
      mpz_class _x = y / 2;
      return mask::ctor::IsNeg_();
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return mask::ctor::IsPos_((2 * p));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return double_mask(sub_mask(p, q));
    } else {
      mpz_class q = y / 2;
      return succ_double_mask(sub_mask(p, q));
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return mask::ctor::IsPos_(pred_double(p));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return double_mask(sub_mask(p, q));
    }
  }
}

std::shared_ptr<Pos::mask> Pos::sub_mask_carry(const mpz_class x,
                                               const mpz_class y) {
  if (x == 1) {
    return mask::ctor::IsNeg_();
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return mask::ctor::IsPos_(pred_double(p));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return double_mask(sub_mask(p, q));
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return double_pred_mask(p);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return double_mask(sub_mask_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return succ_double_mask(sub_mask_carry(p, q));
    }
  }
}

__attribute__((pure)) Comparison Pos::compare_cont(const Comparison r,
                                                   const mpz_class x,
                                                   const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return r;
    } else if (y % 2 != 0) {
      mpz_class _x = (y - 1) / 2;
      return Comparison::e_LT;
    } else {
      mpz_class _x = y / 2;
      return Comparison::e_LT;
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return Comparison::e_GT;
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return compare_cont(r, p, q);
    } else {
      mpz_class q = y / 2;
      return compare_cont(Comparison::e_GT, p, q);
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return Comparison::e_GT;
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return compare_cont(Comparison::e_LT, p, q);
    } else {
      mpz_class q = y / 2;
      return compare_cont(r, p, q);
    }
  }
}

__attribute__((pure)) Comparison Pos::compare(const mpz_class _x0,
                                              const mpz_class _x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
}

__attribute__((pure)) bool Pos::eqb(const mpz_class p, const mpz_class q) {
  if (p == 1) {
    if (q == 1) {
      return true;
    } else if (q % 2 != 0) {
      mpz_class _x = (q - 1) / 2;
      return false;
    } else {
      mpz_class _x = q / 2;
      return false;
    }
  } else if (p % 2 != 0) {
    mpz_class p0 = (p - 1) / 2;
    if (q == 1) {
      return false;
    } else if (q % 2 != 0) {
      mpz_class q0 = (q - 1) / 2;
      return eqb(p0, q0);
    } else {
      mpz_class _x = q / 2;
      return false;
    }
  } else {
    mpz_class p0 = p / 2;
    if (q == 1) {
      return false;
    } else if (q % 2 != 0) {
      mpz_class _x = (q - 1) / 2;
      return false;
    } else {
      mpz_class q0 = q / 2;
      return eqb(p0, q0);
    }
  }
}

__attribute__((pure)) mpz_class Coq_Pos::add_carry(const mpz_class x,
                                                   const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return (2 * mpz_class(1) + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * (q + 1) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * (q + 1));
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return (2 * (p + 1) + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * add_carry(p, q));
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return (2 * (p + 1));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return (2 * (p + q) + 1);
    }
  }
}

__attribute__((pure)) Comparison BinNat::compare(const mpz_class n,
                                                 const mpz_class m) {
  if (n == 0) {
    if (m == 0) {
      return Comparison::e_EQ;
    } else {
      mpz_class _x = m;
      return Comparison::e_LT;
    }
  } else {
    mpz_class n_ = n;
    if (m == 0) {
      return Comparison::e_GT;
    } else {
      mpz_class m_ = m;
      return Pos::compare(n_, m_);
    }
  }
}

__attribute__((pure)) std::pair<mpz_class, mpz_class>
BinNat::pos_div_eucl(const mpz_class a, const mpz_class b) {
  if (a == 1) {
    if (b == 0) {
      return std::make_pair(mpz_class(0), mpz_class(1));
    } else {
      mpz_class p = b;
      if (p == 1) {
        return std::make_pair(mpz_class(1), mpz_class(0));
      } else if (p % 2 != 0) {
        mpz_class _x = (p - 1) / 2;
        return std::make_pair(mpz_class(0), mpz_class(1));
      } else {
        mpz_class _x = p / 2;
        return std::make_pair(mpz_class(0), mpz_class(1));
      }
    }
  } else if (a % 2 != 0) {
    mpz_class a_ = (a - 1) / 2;
    mpz_class q = BinNat::pos_div_eucl(a_, b).first;
    mpz_class r = BinNat::pos_div_eucl(a_, b).second;
    mpz_class r_ = (std::move(r) * 2 + 1);
    if (b <= std::move(r_)) {
      return std::make_pair(
          (q * 2 + 1), (std::move(r_) >= b ? std::move(r_) - b : mpz_class(0)));
    } else {
      return std::make_pair((q * 2), std::move(r_));
    }
  } else {
    mpz_class a_ = a / 2;
    mpz_class q = BinNat::pos_div_eucl(a_, b).first;
    mpz_class r = BinNat::pos_div_eucl(a_, b).second;
    mpz_class r_ = (std::move(r) * 2);
    if (b <= std::move(r_)) {
      return std::make_pair(
          (q * 2 + 1), (std::move(r_) >= b ? std::move(r_) - b : mpz_class(0)));
    } else {
      return std::make_pair((q * 2), std::move(r_));
    }
  }
}

__attribute__((pure)) std::pair<mpz_class, mpz_class>
BinNat::div_eucl(const mpz_class a, const mpz_class b) {
  if (a == 0) {
    return std::make_pair(mpz_class(0), mpz_class(0));
  } else {
    mpz_class na = a;
    if (b == 0) {
      return std::make_pair(mpz_class(0), a);
    } else {
      mpz_class _x = b;
      return BinNat::pos_div_eucl(std::move(na), b);
    }
  }
}

__attribute__((pure)) mpz_class NGMPTest::add_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class NGMPTest::mul_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) mpz_class NGMPTest::sub_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : mpz_class(0));
}

__attribute__((pure)) mpz_class NGMPTest::div_test(const mpz_class _x0,
                                                   const mpz_class _x1) {
  return (_x1 == 0 ? mpz_class(0) : _x0 / _x1);
}

__attribute__((pure)) bool NGMPTest::eqb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool NGMPTest::ltb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool NGMPTest::leb_test(const mpz_class _x0,
                                              const mpz_class _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) mpz_class NGMPTest::succ_test(const mpz_class _x0) {
  return (_x0 + 1);
}

__attribute__((pure)) mpz_class NGMPTest::pred_test(const mpz_class _x0) {
  return (_x0 == 0 ? mpz_class(0) : _x0 - 1);
}

__attribute__((pure)) mpz_class NGMPTest::double_test(const mpz_class _x0) {
  return (_x0 * 2);
}

__attribute__((pure)) bool NGMPTest::is_zero(const mpz_class n) {
  if (n == 0) {
    return true;
  } else {
    mpz_class _x = n;
    return false;
  }
}

__attribute__((pure)) mpz_class NGMPTest::pos_add(const mpz_class _x0,
                                                  const mpz_class _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) mpz_class NGMPTest::pos_succ(const mpz_class _x0) {
  return (_x0 + 1);
}
