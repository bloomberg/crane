#include <well_founded_rec.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) List<unsigned int>
WellFoundedRec::countdown_acc(unsigned int n) {
  if (n <= 0) {
    return List<unsigned int>::cons(0u, List<unsigned int>::nil());
  } else {
    unsigned int m = n - 1;
    return List<unsigned int>::cons(n, countdown_acc(m));
  }
}

__attribute__((pure)) List<unsigned int>
WellFoundedRec::countdown(const unsigned int &_x0) {
  return countdown_acc(_x0);
}

__attribute__((pure)) unsigned int
WellFoundedRec::div2_wf(const unsigned int &x) {
  if (x <= 0) {
    return 0u;
  } else {
    unsigned int n0 = x - 1;
    if (n0 <= 0) {
      return 0u;
    } else {
      unsigned int m = n0 - 1;
      return (div2_wf(m) + 1);
    }
  }
}

__attribute__((pure)) unsigned int WellFoundedRec::gcd_wf(const unsigned int &x,
                                                          unsigned int b) {
  if (x <= 0) {
    return b;
  } else {
    unsigned int a_ = x - 1;
    unsigned int y = ((a_ + 1) ? b % (a_ + 1) : b);
    return gcd_wf(y, (a_ + 1));
  }
}
