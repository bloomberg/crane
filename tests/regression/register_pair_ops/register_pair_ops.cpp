#include <register_pair_ops.h>

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

__attribute__((pure)) unsigned int PeanoNat::sub(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(n);
  } else {
    unsigned int k = n - 1;
    if (m <= 0) {
      return n;
    } else {
      unsigned int l = m - 1;
      return PeanoNat::sub(std::move(k), l);
    }
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

__attribute__((pure)) bool PeanoNat::leb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

__attribute__((pure)) bool PeanoNat::ltb(const unsigned int n,
                                         const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
PeanoNat::divmod(const unsigned int x, const unsigned int y,
                 const unsigned int q, const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return PeanoNat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return PeanoNat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int PeanoNat::div(const unsigned int x,
                                                 const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return PeanoNat::divmod(x, y_, 0u, y_).first;
  }
}

__attribute__((pure)) unsigned int PeanoNat::modulo(const unsigned int x,
                                                    const unsigned int y) {
  if (y <= 0) {
    return std::move(x);
  } else {
    unsigned int y_ = y - 1;
    return PeanoNat::sub(y_, PeanoNat::divmod(x, y_, 0u, y_).second);
  }
}

__attribute__((pure)) unsigned int
RegisterPairOps::get_reg(const std::shared_ptr<RegisterPairOps::state> &s,
                         const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<RegisterPairOps::state>
RegisterPairOps::set_reg(std::shared_ptr<RegisterPairOps::state> s,
                         const unsigned int r, const unsigned int v) {
  return std::make_shared<RegisterPairOps::state>(
      state{update_nth<unsigned int>(std::move(r),
                                     PeanoNat::modulo(std::move(v), 16u),
                                     std::move(s)->regs)});
}

__attribute__((pure)) unsigned int
RegisterPairOps::get_reg_pair(const std::shared_ptr<RegisterPairOps::state> &s,
                              const unsigned int r) {
  unsigned int base =
      (((r - PeanoNat::modulo(r, 2u)) > r ? 0 : (r - PeanoNat::modulo(r, 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<RegisterPairOps::state>
RegisterPairOps::set_reg_pair(const std::shared_ptr<RegisterPairOps::state> &s,
                              const unsigned int r, const unsigned int v) {
  unsigned int base =
      (((r - PeanoNat::modulo(r, 2u)) > r ? 0 : (r - PeanoNat::modulo(r, 2u))));
  unsigned int hi = PeanoNat::div(v, 16u);
  unsigned int lo = PeanoNat::modulo(v, 16u);
  std::shared_ptr<RegisterPairOps::state> s1 =
      set_reg(s, std::move(base), std::move(hi));
  return set_reg(std::move(s1), (std::move(base) + 1u), std::move(lo));
}

__attribute__((pure)) unsigned int
RegisterPairOps::pair_base(const unsigned int r) {
  return (
      ((r - PeanoNat::modulo(r, 2u)) > r ? 0 : (r - PeanoNat::modulo(r, 2u))));
}

__attribute__((pure)) unsigned int
RegisterPairOps::pair_index(const unsigned int r) {
  return PeanoNat::div(r, 2u);
}

__attribute__((pure)) bool
RegisterPairOps::pair_property(const unsigned int r) {
  unsigned int p = pair_index(r);
  return (PeanoNat::ltb(p, 8u) &&
          (PeanoNat::eqb(r, (2u * p)) || PeanoNat::eqb(r, ((2u * p) + 1u))));
}

std::shared_ptr<List<unsigned int>> ListDef::seq(const unsigned int start,
                                                 const unsigned int len) {
  if (len <= 0) {
    return List<unsigned int>::ctor::Nil_();
  } else {
    unsigned int len0 = len - 1;
    return List<unsigned int>::ctor::Cons_(start,
                                           ListDef::seq((start + 1), len0));
  }
}
