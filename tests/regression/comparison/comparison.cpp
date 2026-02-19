#include <algorithm>
#include <any>
#include <comparison.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int Comparison::cmp_to_nat(const Comparison::cmp c) {
  return [&](void) {
    switch (c) {
    case cmp::CmpLt: {
      return 0u;
    }
    case cmp::CmpEq: {
      return 1u;
    }
    case cmp::CmpGt: {
      return 2u;
    }
    }
  }();
}

Comparison::cmp Comparison::compare_nats(const unsigned int a,
                                         const unsigned int b) {
  if ((a < b)) {
    return cmp::CmpLt;
  } else {
    if ((a == b)) {
      return cmp::CmpEq;
    } else {
      return cmp::CmpGt;
    }
  }
}

unsigned int Comparison::max_nat(const unsigned int a, const unsigned int b) {
  return [&](void) {
    switch (compare_nats(a, b)) {
    case cmp::CmpLt: {
      return b;
    }
    case cmp::CmpEq: {
      return a;
    }
    case cmp::CmpGt: {
      return a;
    }
    }
  }();
}

unsigned int Comparison::min_nat(const unsigned int a, const unsigned int b) {
  return [&](void) {
    switch (compare_nats(a, b)) {
    case cmp::CmpLt: {
      return a;
    }
    case cmp::CmpEq: {
      return a;
    }
    case cmp::CmpGt: {
      return b;
    }
    }
  }();
}

unsigned int Comparison::clamp(const unsigned int val0, const unsigned int lo,
                               const unsigned int hi) {
  return [&](void) {
    switch (compare_nats(val0, lo)) {
    case cmp::CmpLt: {
      return lo;
    }
    case cmp::CmpEq: {
      return [&](void) {
        switch (compare_nats(val0, hi)) {
        case cmp::CmpLt: {
          return val0;
        }
        case cmp::CmpEq: {
          return val0;
        }
        case cmp::CmpGt: {
          return hi;
        }
        }
      }();
    }
    case cmp::CmpGt: {
      return [&](void) {
        switch (compare_nats(val0, hi)) {
        case cmp::CmpLt: {
          return val0;
        }
        case cmp::CmpEq: {
          return val0;
        }
        case cmp::CmpGt: {
          return hi;
        }
        }
      }();
    }
    }
  }();
}

Comparison::cmp Comparison::flip_cmp(const Comparison::cmp c) {
  return [&](void) {
    switch (c) {
    case cmp::CmpLt: {
      return cmp::CmpGt;
    }
    case cmp::CmpEq: {
      return cmp::CmpEq;
    }
    case cmp::CmpGt: {
      return cmp::CmpLt;
    }
    }
  }();
}
