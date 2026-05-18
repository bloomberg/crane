// Regression: record projections used as first-class function values
// in separate extraction must render as lambdas (no standalone definition).

#include "SepExtProjectionLambda.h"
#include "Datatypes.h"

#include <iostream>

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

struct BoolSig {
  using A = bool;
};

static_assert(SepExtProjectionLambda::Sig<BoolSig>);

using W = SepExtProjectionLambda::Worker<BoolSig>;

int main() {
  // Build some items
  auto item1 = W::item(10u, true);
  auto item2 = W::item(20u, false);
  auto item3 = W::item(30u, true);

  // Test get_label (projection applied to one arg)
  ASSERT(W::get_label(item1) == 10u);
  ASSERT(W::get_label(item2) == 20u);

  // Test all_labels (projection passed as first-class function to map)
  auto items = Datatypes::List<W::item>::cons(
      item1,
      Datatypes::List<W::item>::cons(
          item2,
          Datatypes::List<W::item>::cons(
              item3, Datatypes::List<W::item>::nil())));
  auto labels = W::all_labels(items);
  const auto &[h1, t1] =
      std::get<typename Datatypes::List<uint64_t>::Cons>(labels.v());
  ASSERT(h1 == 10u);

  // Test find_label (projection used in function body)
  auto found = W::find_label(20u, items);
  ASSERT(found.has_value());
  ASSERT(*found == false);

  auto not_found = W::find_label(99u, items);
  ASSERT(!not_found.has_value());

  return testStatus;
}
