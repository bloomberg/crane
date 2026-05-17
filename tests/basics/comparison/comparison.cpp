#include "comparison.h"

unsigned int Comparison::cmp_to_nat(Comparison::Cmp c) {
  switch (c) {
  case Cmp::CMPLT: {
    return 0u;
  }
  case Cmp::CMPEQ: {
    return 1u;
  }
  case Cmp::CMPGT: {
    return 2u;
  }
  default:
    std::unreachable();
  }
}

Comparison::Cmp Comparison::compare_nats(unsigned int a, unsigned int b) {
  if (a < b) {
    return Cmp::CMPLT;
  } else {
    if (a == b) {
      return Cmp::CMPEQ;
    } else {
      return Cmp::CMPGT;
    }
  }
}

unsigned int Comparison::max_nat(unsigned int a, unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::CMPLT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

unsigned int Comparison::min_nat(unsigned int a, unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::CMPGT: {
    return b;
  }
  default: {
    return a;
  }
  }
}

unsigned int Comparison::clamp(unsigned int val, unsigned int lo,
                               unsigned int hi) {
  switch (compare_nats(val, lo)) {
  case Cmp::CMPLT: {
    return lo;
  }
  default: {
    switch (compare_nats(val, hi)) {
    case Cmp::CMPGT: {
      return hi;
    }
    default: {
      return val;
    }
    }
  }
  }
}

Comparison::Cmp Comparison::flip_cmp(Comparison::Cmp c) {
  switch (c) {
  case Cmp::CMPLT: {
    return Cmp::CMPGT;
  }
  case Cmp::CMPEQ: {
    return Cmp::CMPEQ;
  }
  case Cmp::CMPGT: {
    return Cmp::CMPLT;
  }
  default:
    std::unreachable();
  }
}
