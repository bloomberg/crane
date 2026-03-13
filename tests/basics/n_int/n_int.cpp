#include <n_int.h>

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

__attribute__((pure)) unsigned int Pos::succ(const unsigned int x) {
  if (x == 1u) {
    return (2u * 1u);
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * succ(p));
  } else {
    unsigned int p = x / 2u;
    return (2u * p + 1u);
  }
}

__attribute__((pure)) unsigned int Pos::pred_double(const unsigned int x) {
  if (x == 1u) {
    return 1u;
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * (2u * p) + 1u);
  } else {
    unsigned int p = x / 2u;
    return (2u * pred_double(p) + 1u);
  }
}

__attribute__((pure)) unsigned int Pos::pred_N(const unsigned int x) {
  if (x == 1u) {
    return 0u;
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return (2u * p);
  } else {
    unsigned int p = x / 2u;
    return pred_double(p);
  }
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsPos_(1u); },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            unsigned int p = _args.d_a0;
            return mask::ctor::IsPos_((2u * std::move(p) + 1u));
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
            unsigned int p = _args.d_a0;
            return mask::ctor::IsPos_((2u * std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask> Pos::double_pred_mask(const unsigned int x) {
  if (x == 1u) {
    return mask::ctor::IsNul_();
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return mask::ctor::IsPos_((2u * (2u * p)));
  } else {
    unsigned int p = x / 2u;
    return mask::ctor::IsPos_((2u * pred_double(p)));
  }
}

std::shared_ptr<Pos::mask> Pos::sub_mask(const unsigned int x,
                                         const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return mask::ctor::IsNul_();
    } else if (y % 2u != 0u) {
      unsigned int _x = (y - 1u) / 2u;
      return mask::ctor::IsNeg_();
    } else {
      unsigned int _x = y / 2u;
      return mask::ctor::IsNeg_();
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return mask::ctor::IsPos_((2u * p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return double_mask(sub_mask(p, q));
    } else {
      unsigned int q = y / 2u;
      return succ_double_mask(sub_mask(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return mask::ctor::IsPos_(pred_double(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return double_mask(sub_mask(p, q));
    }
  }
}

std::shared_ptr<Pos::mask> Pos::sub_mask_carry(const unsigned int x,
                                               const unsigned int y) {
  if (x == 1u) {
    return mask::ctor::IsNeg_();
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return mask::ctor::IsPos_(pred_double(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return double_mask(sub_mask(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return double_pred_mask(p);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return double_mask(sub_mask_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return succ_double_mask(sub_mask_carry(p, q));
    }
  }
}

__attribute__((pure)) Comparison Pos::compare_cont(const Comparison r,
                                                   const unsigned int x,
                                                   const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return r;
    } else if (y % 2u != 0u) {
      unsigned int _x = (y - 1u) / 2u;
      return Comparison::e_LT;
    } else {
      unsigned int _x = y / 2u;
      return Comparison::e_LT;
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return Comparison::e_GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(r, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(Comparison::e_GT, p, q);
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return Comparison::e_GT;
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return compare_cont(Comparison::e_LT, p, q);
    } else {
      unsigned int q = y / 2u;
      return compare_cont(r, p, q);
    }
  }
}

__attribute__((pure)) Comparison Pos::compare(const unsigned int _x0,
                                              const unsigned int _x1) {
  return compare_cont(Comparison::e_EQ, _x0, _x1);
}

__attribute__((pure)) bool Pos::eqb(const unsigned int p,
                                    const unsigned int q) {
  if (p == 1u) {
    if (q == 1u) {
      return true;
    } else if (q % 2u != 0u) {
      unsigned int _x = (q - 1u) / 2u;
      return false;
    } else {
      unsigned int _x = q / 2u;
      return false;
    }
  } else if (p % 2u != 0u) {
    unsigned int p0 = (p - 1u) / 2u;
    if (q == 1u) {
      return false;
    } else if (q % 2u != 0u) {
      unsigned int q0 = (q - 1u) / 2u;
      return eqb(p0, q0);
    } else {
      unsigned int _x = q / 2u;
      return false;
    }
  } else {
    unsigned int p0 = p / 2u;
    if (q == 1u) {
      return false;
    } else if (q % 2u != 0u) {
      unsigned int _x = (q - 1u) / 2u;
      return false;
    } else {
      unsigned int q0 = q / 2u;
      return eqb(p0, q0);
    }
  }
}

__attribute__((pure)) unsigned int Coq_Pos::add_carry(const unsigned int x,
                                                      const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return (2u * 1u + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * (q + 1u) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * (q + 1u));
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return (2u * (p + 1u) + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * add_carry(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return (2u * (p + 1u));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return (2u * (p + q) + 1u);
    }
  }
}

__attribute__((pure)) Comparison BinNat::compare(const unsigned int n,
                                                 const unsigned int m) {
  if (n == 0u) {
    if (m == 0u) {
      return Comparison::e_EQ;
    } else {
      unsigned int _x = m;
      return Comparison::e_LT;
    }
  } else {
    unsigned int n_ = n;
    if (m == 0u) {
      return Comparison::e_GT;
    } else {
      unsigned int m_ = m;
      return Pos::compare(n_, m_);
    }
  }
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
BinNat::pos_div_eucl(const unsigned int a, const unsigned int b) {
  if (a == 1u) {
    if (b == 0u) {
      return std::make_pair(0u, 1u);
    } else {
      unsigned int p = b;
      if (p == 1u) {
        return std::make_pair(1u, 0u);
      } else if (p % 2u != 0u) {
        unsigned int _x = (p - 1u) / 2u;
        return std::make_pair(0u, 1u);
      } else {
        unsigned int _x = p / 2u;
        return std::make_pair(0u, 1u);
      }
    }
  } else if (a % 2u != 0u) {
    unsigned int a_ = (a - 1u) / 2u;
    unsigned int q = BinNat::pos_div_eucl(a_, b).first;
    unsigned int r = BinNat::pos_div_eucl(a_, b).second;
    unsigned int r_ = (std::move(r) * 2u + 1u);
    if (b <= std::move(r_)) {
      return std::make_pair((q * 2u + 1u),
                            (std::move(r_) >= b ? std::move(r_) - b : 0u));
    } else {
      return std::make_pair((q * 2u), std::move(r_));
    }
  } else {
    unsigned int a_ = a / 2u;
    unsigned int q = BinNat::pos_div_eucl(a_, b).first;
    unsigned int r = BinNat::pos_div_eucl(a_, b).second;
    unsigned int r_ = (std::move(r) * 2u);
    if (b <= std::move(r_)) {
      return std::make_pair((q * 2u + 1u),
                            (std::move(r_) >= b ? std::move(r_) - b : 0u));
    } else {
      return std::make_pair((q * 2u), std::move(r_));
    }
  }
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
BinNat::div_eucl(const unsigned int a, const unsigned int b) {
  if (a == 0u) {
    return std::make_pair(0u, 0u);
  } else {
    unsigned int na = a;
    if (b == 0u) {
      return std::make_pair(0u, a);
    } else {
      unsigned int _x = b;
      return BinNat::pos_div_eucl(std::move(na), b);
    }
  }
}

__attribute__((pure)) unsigned int NIntTest::add_test(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int NIntTest::mul_test(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) unsigned int NIntTest::sub_test(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x0 >= _x1 ? _x0 - _x1 : 0u);
}

__attribute__((pure)) unsigned int NIntTest::div_test(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x1 == 0u ? 0u : _x0 / _x1);
}

__attribute__((pure)) bool NIntTest::eqb_test(const unsigned int _x0,
                                              const unsigned int _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool NIntTest::ltb_test(const unsigned int _x0,
                                              const unsigned int _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool NIntTest::leb_test(const unsigned int _x0,
                                              const unsigned int _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) unsigned int NIntTest::succ_test(const unsigned int _x0) {
  return (_x0 + 1u);
}

__attribute__((pure)) unsigned int NIntTest::pred_test(const unsigned int _x0) {
  return (_x0 == 0u ? 0u : _x0 - 1u);
}

__attribute__((pure)) unsigned int
NIntTest::double_test(const unsigned int _x0) {
  return (_x0 * 2u);
}

__attribute__((pure)) bool NIntTest::is_zero(const unsigned int n) {
  if (n == 0u) {
    return true;
  } else {
    unsigned int _x = n;
    return false;
  }
}

__attribute__((pure)) unsigned int NIntTest::pos_add(const unsigned int _x0,
                                                     const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int NIntTest::pos_succ(const unsigned int _x0) {
  return (_x0 + 1u);
}
