#include "comparison.h"

uint64_t Comparison::cmp_to_nat(Comparison::Cmp c) {
  switch (c) {
  case Cmp::CMPLT: {
    return UINT64_C(0);
  } break;
  case Cmp::CMPEQ: {
    return UINT64_C(1);
  } break;
  case Cmp::CMPGT: {
    return UINT64_C(2);
  } break;
  default:
    std::unreachable();
  }
}

Comparison::Cmp Comparison::compare_nats(uint64_t a, uint64_t b) {
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

uint64_t Comparison::max_nat(uint64_t a, uint64_t b) {
  switch (compare_nats(a, b)) {
  case Cmp::CMPLT: {
    return b;
  } break;
  default: {
    return a;
  }
  }
}

uint64_t Comparison::min_nat(uint64_t a, uint64_t b) {
  switch (compare_nats(a, b)) {
  case Cmp::CMPGT: {
    return b;
  } break;
  default: {
    return a;
  }
  }
}

uint64_t Comparison::clamp(uint64_t val, uint64_t lo, uint64_t hi) {
  switch (compare_nats(val, lo)) {
  case Cmp::CMPLT: {
    return lo;
  } break;
  default: {
    switch (compare_nats(val, hi)) {
    case Cmp::CMPGT: {
      return hi;
    } break;
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
  } break;
  case Cmp::CMPEQ: {
    return Cmp::CMPEQ;
  } break;
  case Cmp::CMPGT: {
    return Cmp::CMPLT;
  } break;
  default:
    std::unreachable();
  }
}
