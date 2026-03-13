#include <z_int.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

__attribute__((pure)) unsigned int Pos::add(const unsigned int x,
                                            const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return (2u * 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * succ(q));
    } else {
      unsigned int q = y / 2u;
      return (2u * q + 1u);
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return (2u * succ(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return (2u * add(p, q) + 1u);
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return (2u * p + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add(p, q) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * add(p, q));
    }
  }
}

__attribute__((pure)) unsigned int Pos::add_carry(const unsigned int x,
                                                  const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return (2u * 1u + 1u);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * succ(q) + 1u);
    } else {
      unsigned int q = y / 2u;
      return (2u * succ(q));
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return (2u * succ(p) + 1u);
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
      return (2u * succ(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (2u * add_carry(p, q));
    } else {
      unsigned int q = y / 2u;
      return (2u * add(p, q) + 1u);
    }
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

__attribute__((pure)) unsigned int Pos::mul(const unsigned int x,
                                            const unsigned int y) {
  if (x == 1u) {
    return std::move(y);
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    return add(y, (2u * mul(std::move(p), y)));
  } else {
    unsigned int p = x / 2u;
    return (2u * mul(std::move(p), y));
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

__attribute__((pure)) int64_t BinInt::double_(const int64_t x) {
  if (x == 0) {
    return INT64_C(0);
  } else if (x > 0) {
    unsigned int p = static_cast<unsigned int>(x);
    return static_cast<int64_t>((2u * p));
  } else {
    unsigned int p = static_cast<unsigned int>(-x);
    return (-static_cast<int64_t>((2u * p)));
  }
}

__attribute__((pure)) int64_t BinInt::succ_double(const int64_t x) {
  if (x == 0) {
    return static_cast<int64_t>(1u);
  } else if (x > 0) {
    unsigned int p = static_cast<unsigned int>(x);
    return static_cast<int64_t>((2u * p + 1u));
  } else {
    unsigned int p = static_cast<unsigned int>(-x);
    return (-static_cast<int64_t>(Pos::pred_double(p)));
  }
}

__attribute__((pure)) int64_t BinInt::pred_double(const int64_t x) {
  if (x == 0) {
    return (-static_cast<int64_t>(1u));
  } else if (x > 0) {
    unsigned int p = static_cast<unsigned int>(x);
    return static_cast<int64_t>(Pos::pred_double(p));
  } else {
    unsigned int p = static_cast<unsigned int>(-x);
    return (-static_cast<int64_t>((2u * p + 1u)));
  }
}

__attribute__((pure)) int64_t BinInt::pos_sub(const unsigned int x,
                                              const unsigned int y) {
  if (x == 1u) {
    if (y == 1u) {
      return INT64_C(0);
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return (-static_cast<int64_t>((2u * q)));
    } else {
      unsigned int q = y / 2u;
      return (-static_cast<int64_t>(Pos::pred_double(q)));
    }
  } else if (x % 2u != 0u) {
    unsigned int p = (x - 1u) / 2u;
    if (y == 1u) {
      return static_cast<int64_t>((2u * p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return BinInt::double_(BinInt::pos_sub(p, q));
    } else {
      unsigned int q = y / 2u;
      return BinInt::succ_double(BinInt::pos_sub(p, q));
    }
  } else {
    unsigned int p = x / 2u;
    if (y == 1u) {
      return static_cast<int64_t>(Pos::pred_double(p));
    } else if (y % 2u != 0u) {
      unsigned int q = (y - 1u) / 2u;
      return BinInt::pred_double(BinInt::pos_sub(p, q));
    } else {
      unsigned int q = y / 2u;
      return BinInt::double_(BinInt::pos_sub(p, q));
    }
  }
}

__attribute__((pure)) Comparison BinInt::compare(const int64_t x,
                                                 const int64_t y) {
  if (x == 0) {
    if (y == 0) {
      return Comparison::e_EQ;
    } else if (y > 0) {
      unsigned int _x = static_cast<unsigned int>(y);
      return Comparison::e_LT;
    } else {
      unsigned int _x = static_cast<unsigned int>(-y);
      return Comparison::e_GT;
    }
  } else if (x > 0) {
    unsigned int x_ = static_cast<unsigned int>(x);
    if (y == 0) {
      return Comparison::e_GT;
    } else if (y > 0) {
      unsigned int y_ = static_cast<unsigned int>(y);
      return Pos::compare(x_, y_);
    } else {
      unsigned int _x = static_cast<unsigned int>(-y);
      return Comparison::e_GT;
    }
  } else {
    unsigned int x_ = static_cast<unsigned int>(-x);
    if (y == 0) {
      return Comparison::e_LT;
    } else if (y > 0) {
      unsigned int _x = static_cast<unsigned int>(y);
      return Comparison::e_LT;
    } else {
      unsigned int y_ = static_cast<unsigned int>(-y);
      return Datatypes::CompOpp(Pos::compare(x_, y_));
    }
  }
}

__attribute__((pure)) int64_t ZIntTest::add_test(const int64_t _x0,
                                                 const int64_t _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) int64_t ZIntTest::mul_test(const int64_t _x0,
                                                 const int64_t _x1) {
  return (_x0 * _x1);
}

__attribute__((pure)) int64_t ZIntTest::sub_test(const int64_t _x0,
                                                 const int64_t _x1) {
  return (_x0 - _x1);
}

__attribute__((pure)) int64_t ZIntTest::abs_test(const int64_t _x0) {
  return std::abs(_x0);
}

__attribute__((pure)) int64_t ZIntTest::opp_test(const int64_t _x0) {
  return (-_x0);
}

__attribute__((pure)) bool ZIntTest::eqb_test(const int64_t _x0,
                                              const int64_t _x1) {
  return _x0 == _x1;
}

__attribute__((pure)) bool ZIntTest::ltb_test(const int64_t _x0,
                                              const int64_t _x1) {
  return _x0 < _x1;
}

__attribute__((pure)) bool ZIntTest::leb_test(const int64_t _x0,
                                              const int64_t _x1) {
  return _x0 <= _x1;
}

__attribute__((pure)) int64_t ZIntTest::z_sign(const int64_t z) {
  if (z == 0) {
    return INT64_C(0);
  } else if (z > 0) {
    unsigned int _x = static_cast<unsigned int>(z);
    return static_cast<int64_t>(1u);
  } else {
    unsigned int _x = static_cast<unsigned int>(-z);
    return (-static_cast<int64_t>(1u));
  }
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
