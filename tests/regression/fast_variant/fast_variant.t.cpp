// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <fast_variant.h>

#include <cstdint>
#include <iostream>
#include <variant>
#include <vector>

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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using FV = FastVariant;

// A match written by hand, as a user of the extracted type writes it.
static std::vector<uint64_t> elements(const List<uint64_t> &l) {
  std::vector<uint64_t> out;
  const List<uint64_t> *p = &l;
  while (const auto *c = crane::get_if<List<uint64_t>::Cons>(&p->v())) {
    const auto &[x, rest] = *c;
    out.push_back(x);
    p = rest.get();
  }
  return out;
}

int main() {
  // Value-type inductive: building it copies and moves variants; the
  // loopified methods keep their frames in one as well.
  ASSERT(FV::sample.sum() == 28);
  ASSERT(FV::sample.size() == 6);
  ASSERT(FV::sample.insert(4).sum() == 32);
  ASSERT(crane::holds_alternative<FV::tree::Node>(FV::sample.v()));

  // Copies and assignments of a value keep it intact.
  FV::tree t = FV::sample;
  FV::tree u = FV::tree::leaf();
  ASSERT(crane::holds_alternative<FV::tree::Leaf>(u.v()));
  u = t;
  ASSERT(u.sum() == 28 && t.sum() == 28);
  u = FV::tree::leaf();
  ASSERT(u.size() == 0 && t.size() == 6);

  // Three alternatives, matched through get.
  std::vector<uint64_t> areas;
  const List<FV::shape> *p = &FV::shapes;
  while (crane::holds_alternative<List<FV::shape>::Cons>(p->v())) {
    const auto &[s, rest] = crane::get<List<FV::shape>::Cons>(p->v());
    areas.push_back(s.area());
    p = rest.get();
  }
  ASSERT((areas == std::vector<uint64_t>{12, 12, 0}));

  // A wrong alternative is reported as std::variant reports it.
  bool threw = false;
  try {
    (void)crane::get<FV::tree::Leaf>(FV::sample.v());
  } catch (const std::bad_variant_access &) {
    threw = true;
  }
  ASSERT(threw);

  // Coinductive: the lazy cell forces into a variant.
  ASSERT((elements(FV::first_three) == std::vector<uint64_t>{10, 11, 12}));

  if (testStatus == 0) {
    std::cout << "All fast_variant tests passed!" << std::endl;
  }
  return testStatus;
}
