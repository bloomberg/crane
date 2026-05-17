// Regression: nullary definitions in separate extraction must be called
// with (), not used as bare function references.

#include "SepExtNullaryCall.h"
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

struct MyCfg {
  static const unsigned int &default_val() {
    static const unsigned int v = 42u;
    return v;
  }

  static const Datatypes::List<uint64_t> &default_list() {
    static const Datatypes::List<uint64_t> v =
        Datatypes::List<uint64_t>::cons(
            10u, Datatypes::List<uint64_t>::cons(
                     20u, Datatypes::List<uint64_t>::nil()));
    return v;
  }
};

static_assert(SepExtNullaryCall::Cfg<MyCfg>);

using W = SepExtNullaryCall::Worker<MyCfg>;

int main() {
  ASSERT(W::get_default() == 42u);
  ASSERT(W::local_length() == 0u);

  auto prepended = W::prepend(5u);
  const auto &[h, t] =
      std::get<typename Datatypes::List<uint64_t>::Cons>(prepended.v());
  ASSERT(h == 5u);

  ASSERT(W::default_head() == 10u);

  return testStatus;
}
