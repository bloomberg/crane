#include <comparison.h>

#include <type_traits>
#include <utility>

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
Comparison::compare_nats(const unsigned int a, const unsigned int b) {
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

__attribute__((pure)) unsigned int Comparison::max_nat(const unsigned int a,
                                                       const unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::e_CMPLT: {
    return std::move(b);
  }
  case Cmp::e_CMPEQ: {
    return std::move(a);
  }
  case Cmp::e_CMPGT: {
    return std::move(a);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int Comparison::min_nat(const unsigned int a,
                                                       const unsigned int b) {
  switch (compare_nats(a, b)) {
  case Cmp::e_CMPLT: {
    return std::move(a);
  }
  case Cmp::e_CMPEQ: {
    return std::move(a);
  }
  case Cmp::e_CMPGT: {
    return std::move(b);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int Comparison::clamp(const unsigned int val,
                                                     const unsigned int lo,
                                                     const unsigned int hi) {
  switch (compare_nats(val, lo)) {
  case Cmp::e_CMPLT: {
    return std::move(lo);
  }
  case Cmp::e_CMPEQ: {
    switch (compare_nats(val, hi)) {
    case Cmp::e_CMPLT: {
      return std::move(val);
    }
    case Cmp::e_CMPEQ: {
      return std::move(val);
    }
    case Cmp::e_CMPGT: {
      return std::move(hi);
    }
    default:
      std::unreachable();
    }
  }
  case Cmp::e_CMPGT: {
    switch (compare_nats(val, hi)) {
    case Cmp::e_CMPLT: {
      return std::move(val);
    }
    case Cmp::e_CMPEQ: {
      return std::move(val);
    }
    case Cmp::e_CMPGT: {
      return std::move(hi);
    }
    default:
      std::unreachable();
    }
  }
  default:
    std::unreachable();
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
