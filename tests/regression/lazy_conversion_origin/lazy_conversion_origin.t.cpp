// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "lazy_conversion_origin.h"

#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(...) aSsErT(!(__VA_ARGS__), #__VA_ARGS__, __LINE__);

using M = LazyConversionOrigin;

// A value that counts how many of it are alive, so that a test sees a
// conversion let go of its source.
struct probe {
  static inline int live = 0;
  long v;
  explicit probe(long x) : v(x) { ++live; }
  probe(const probe &o) : v(o.v) { ++live; }
  probe(probe &&o) noexcept : v(o.v) { ++live; }
  ~probe() { --live; }
};

// A second instantiation for [probe] to convert to and from.
struct other {
  long v;
};

int main() {
  // The generated stream: suspensions run once each, through smap's layers.
  ASSERT(M::doubled(0) == 0);
  ASSERT(M::doubled(5) == 10);
  ASSERT(M::nth(3, M::from(4)) == 7);

  {
    // A conversion out and back is the source itself: the same value.
    crane::lazy<probe> src(probe(3));
    int out_runs = 0, back_runs = 0;
    auto out = crane::lazy<other>::converted_from(src, [src, &out_runs]() mutable -> other {
      ++out_runs;
      return other{src.force().v * 10};
    });
    auto back = crane::lazy<probe>::converted_from(out, [out, &back_runs]() mutable -> probe {
      ++back_runs;
      return probe(out.force().v / 10);
    });
    ASSERT(&back.force() == &src.force());
    ASSERT(back_runs == 0);
    // The conversion itself runs once, whichever copy forces it.
    auto out2 = out;
    ASSERT(out.force().v == 30);
    ASSERT(out2.force().v == 30);
    ASSERT(&out.force() == &out2.force());
    ASSERT(out_runs == 1);

    // Converting onward to a third instantiation is not a round trip.
    int third_runs = 0;
    auto third = crane::lazy<long>::converted_from(out, [out, &third_runs]() mutable -> long {
      ++third_runs;
      return out.force().v + 1;
    });
    ASSERT(third.force() == 31);
    ASSERT(third.force() == 31);
    ASSERT(third_runs == 1);
  }
  // Every node let go of its source with it.
  ASSERT(probe::live == 0);

  {
    // A converted node whose source is gone still holds it: the source's
    // last handle may be the conversion's.
    auto out = [] {
      crane::lazy<probe> src(probe(5));
      return crane::lazy<other>::converted_from(
          src, [src]() mutable -> other { return other{src.force().v}; });
    }();
    ASSERT(probe::live == 1);
    auto back = crane::lazy<probe>::converted_from(
        out, [out]() mutable -> probe { return probe(out.force().v); });
    ASSERT(back.force().v == 5);
    ASSERT(probe::live == 1);
  }
  ASSERT(probe::live == 0);

  {
    // A conversion that throws is not run again: its exception is kept and
    // rethrown by every later force.
    crane::lazy<probe> src(probe(1));
    int runs = 0;
    auto bad = crane::lazy<other>::converted_from(src, [&runs]() mutable -> other {
      ++runs;
      throw std::runtime_error("boom");
    });
    std::string first, second;
    try {
      (void)bad.force();
    } catch (const std::runtime_error &e) {
      first = e.what();
    }
    try {
      (void)bad.force();
    } catch (const std::runtime_error &e) {
      second = e.what();
    }
    ASSERT(first == "boom");
    ASSERT(second == "boom");
    ASSERT(runs == 1);
    // Its round trip is still the source, which never threw.
    auto back = crane::lazy<probe>::converted_from(
        bad, [bad]() mutable -> probe { return probe(bad.force().v); });
    ASSERT(back.force().v == 1);
  }
  ASSERT(probe::live == 0);

  {
    // A conversion of a value that holds nothing is a plain suspension.
    crane::lazy<probe> empty;
    int runs = 0;
    auto out = crane::lazy<other>::converted_from(empty, [&runs]() mutable -> other {
      ++runs;
      return other{9};
    });
    ASSERT(out.force().v == 9);
    auto back = crane::lazy<probe>::converted_from(out, [out]() mutable -> probe {
      return probe(out.force().v);
    });
    ASSERT(back.force().v == 9);
    ASSERT(runs == 1);
  }
  ASSERT(probe::live == 0);

  {
    // A plain suspension (no source) that produces another cell delegates
    // to it, and a converted cell can be what it produces.
    crane::lazy<probe> src(probe(2));
    auto out = crane::lazy<other>::converted_from(
        src, [src]() mutable -> other { return other{src.force().v}; });
    auto d = crane::lazy<other>::delegate([out]() mutable { return out; });
    ASSERT(d.force().v == 2);
    ASSERT(&d.force() == &out.force());
  }
  ASSERT(probe::live == 0);

  return testStatus;
}
