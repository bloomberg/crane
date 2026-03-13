#include <comparison.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
Comparison::cmp_to_nat(const Comparison::Cmp c) {
  return [&](void) {
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
    }
  }();
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
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int Comparison::min_nat(const unsigned int a,
                                                       const unsigned int b) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int Comparison::clamp(const unsigned int val,
                                                     const unsigned int lo,
                                                     const unsigned int hi) {
  return [&](void) {
    switch (compare_nats(val, lo)) {
    case Cmp::e_CMPLT: {
      return std::move(lo);
    }
    case Cmp::e_CMPEQ: {
      return [&](void) {
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
        }
      }();
    }
    case Cmp::e_CMPGT: {
      return [&](void) {
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
        }
      }();
    }
    }
  }();
}

__attribute__((pure)) Comparison::Cmp
Comparison::flip_cmp(const Comparison::Cmp c) {
  return [&](void) {
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
    }
  }();
}
