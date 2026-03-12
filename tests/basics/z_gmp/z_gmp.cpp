#include <z_gmp.h>

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
#include <variant>

mpz_class Pos::succ(const mpz_class x) {
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

mpz_class Pos::add(const mpz_class x, const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return (2 * mpz_class(1));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * succ(q));
    } else {
      mpz_class q = y / 2;
      return (2 * q + 1);
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return (2 * succ(p));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return (2 * add(p, q) + 1);
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return (2 * p + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add(p, q) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * add(p, q));
    }
  }
}

mpz_class Pos::add_carry(const mpz_class x, const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return (2 * mpz_class(1) + 1);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * succ(q) + 1);
    } else {
      mpz_class q = y / 2;
      return (2 * succ(q));
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return (2 * succ(p) + 1);
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
      return (2 * succ(p));
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (2 * add_carry(p, q));
    } else {
      mpz_class q = y / 2;
      return (2 * add(p, q) + 1);
    }
  }
}

mpz_class Pos::pred_double(const mpz_class x) {
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

mpz_class Pos::mul(const mpz_class x, const mpz_class y) {
  if (x == 1) {
    return std::move(y);
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    return add(y, (2 * mul(std::move(p), y)));
  } else {
    mpz_class p = x / 2;
    return (2 * mul(std::move(p), y));
  }
}

comparison Pos::compare_cont(const comparison r, const mpz_class x,
                             const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return r;
    } else if (y % 2 != 0) {
      mpz_class _x = (y - 1) / 2;
      return comparison::Lt;
    } else {
      mpz_class _x = y / 2;
      return comparison::Lt;
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return comparison::Gt;
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return compare_cont(r, p, q);
    } else {
      mpz_class q = y / 2;
      return compare_cont(comparison::Gt, p, q);
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return comparison::Gt;
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return compare_cont(comparison::Lt, p, q);
    } else {
      mpz_class q = y / 2;
      return compare_cont(r, p, q);
    }
  }
}

comparison Pos::compare(const mpz_class _x0, const mpz_class _x1) {
  return compare_cont(comparison::Eq, _x0, _x1);
}

bool Pos::eqb(const mpz_class p, const mpz_class q) {
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

mpz_class BinInt::double_(const mpz_class x) {
  if (x == 0) {
    return mpz_class(0);
  } else if (x > 0) {
    mpz_class p = x;
    return (2 * p);
  } else {
    mpz_class p = -x;
    return (-(2 * p));
  }
}

mpz_class BinInt::succ_double(const mpz_class x) {
  if (x == 0) {
    return mpz_class(1);
  } else if (x > 0) {
    mpz_class p = x;
    return (2 * p + 1);
  } else {
    mpz_class p = -x;
    return (-Pos::pred_double(p));
  }
}

mpz_class BinInt::pred_double(const mpz_class x) {
  if (x == 0) {
    return (-mpz_class(1));
  } else if (x > 0) {
    mpz_class p = x;
    return Pos::pred_double(p);
  } else {
    mpz_class p = -x;
    return (-(2 * p + 1));
  }
}

mpz_class BinInt::pos_sub(const mpz_class x, const mpz_class y) {
  if (x == 1) {
    if (y == 1) {
      return mpz_class(0);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return (-(2 * q));
    } else {
      mpz_class q = y / 2;
      return (-Pos::pred_double(q));
    }
  } else if (x % 2 != 0) {
    mpz_class p = (x - 1) / 2;
    if (y == 1) {
      return (2 * p);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return BinInt::double_(BinInt::pos_sub(p, q));
    } else {
      mpz_class q = y / 2;
      return BinInt::succ_double(BinInt::pos_sub(p, q));
    }
  } else {
    mpz_class p = x / 2;
    if (y == 1) {
      return Pos::pred_double(p);
    } else if (y % 2 != 0) {
      mpz_class q = (y - 1) / 2;
      return BinInt::pred_double(BinInt::pos_sub(p, q));
    } else {
      mpz_class q = y / 2;
      return BinInt::double_(BinInt::pos_sub(p, q));
    }
  }
}

comparison BinInt::compare(const mpz_class x, const mpz_class y) {
  if (x == 0) {
    if (y == 0) {
      return comparison::Eq;
    } else if (y > 0) {
      mpz_class _x = y;
      return comparison::Lt;
    } else {
      mpz_class _x = -y;
      return comparison::Gt;
    }
  } else if (x > 0) {
    mpz_class x_ = x;
    if (y == 0) {
      return comparison::Gt;
    } else if (y > 0) {
      mpz_class y_ = y;
      return Pos::compare(x_, y_);
    } else {
      mpz_class _x = -y;
      return comparison::Gt;
    }
  } else {
    mpz_class x_ = -x;
    if (y == 0) {
      return comparison::Lt;
    } else if (y > 0) {
      mpz_class _x = y;
      return comparison::Lt;
    } else {
      mpz_class y_ = -y;
      return Datatypes::CompOpp(Pos::compare(x_, y_));
    }
  }
}

mpz_class ZGMPTest::add_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 + _x1);
}

mpz_class ZGMPTest::mul_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 * _x1);
}

mpz_class ZGMPTest::sub_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 - _x1);
}

mpz_class ZGMPTest::abs_test(const mpz_class _x0) { return abs(_x0); }

mpz_class ZGMPTest::opp_test(const mpz_class _x0) { return (-_x0); }

bool ZGMPTest::eqb_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 == _x1);
}

bool ZGMPTest::ltb_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 < _x1);
}

bool ZGMPTest::leb_test(const mpz_class _x0, const mpz_class _x1) {
  return (_x0 <= _x1);
}

mpz_class ZGMPTest::z_sign(const mpz_class z) {
  if (z == 0) {
    return mpz_class(0);
  } else if (z > 0) {
    mpz_class _x = z;
    return mpz_class(1);
  } else {
    mpz_class _x = -z;
    return (-mpz_class(1));
  }
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
