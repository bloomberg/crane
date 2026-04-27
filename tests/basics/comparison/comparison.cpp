#include <comparison.h>

__attribute__((pure)) unsigned int
Comparison::cmp_to_nat(const Comparison::Cmp c) {
  switch (c) {
  case Cmp::e_CMPLT: {
    return 0u;
  }
  case Cmp::e_CMPEQ: {
    return 1u;
  }
  case Cmp::e_CMPGT: {
    return 2u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) Comparison::Cmp
Comparison::compare_nats(const unsigned int &a, const unsigned int &b) {
  if (a < b) {
    return Cmp::e_CMPLT;
  } else {
    if (a == b) {
      return Cmp::e_CMPEQ;
    } else {
      return Cmp::e_CMPGT;
    }
  }
}

__attribute__((pure)) unsigned int Comparison::max_nat(unsigned int a,
                                                       unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::e_CMPLT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

__attribute__((pure)) unsigned int Comparison::min_nat(unsigned int a,
                                                       unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::e_CMPGT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

__attribute__((pure)) unsigned int
Comparison::clamp(unsigned int val, unsigned int lo, unsigned int hi) {
  switch (compare_nats(val, lo)) {
  case Cmp::e_CMPLT: {
    return lo;
  }
  default: {
    switch (compare_nats(val, hi)) {
    case Cmp::e_CMPGT: {
      return hi;
    }
    default: {
      return val;
    }
    }
  }
  }
}

__attribute__((pure)) Comparison::Cmp
Comparison::flip_cmp(const Comparison::Cmp c) {
  switch (c) {
  case Cmp::e_CMPLT: {
    return Cmp::e_CMPGT;
  }
  case Cmp::e_CMPEQ: {
    return Cmp::e_CMPEQ;
  }
  case Cmp::e_CMPGT: {
    return Cmp::e_CMPLT;
  }
  default:
    std::unreachable();
  }
}
