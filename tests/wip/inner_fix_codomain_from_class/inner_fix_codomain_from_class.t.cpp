#include <cassert>
#include <inner_fix_codomain_from_class.h>

struct PT {
  using ptr = uint64_t;
  static ptr zero_ptr() { return 3; }
};
struct IPT {
  using iptr = uint64_t;
  static iptr zero_iptr() { return 5; }
};
struct P {
  using PTR = PT;
  using IPTR = IPT;
};

int main() {
  auto r = InnerFixCodomainFromClass::use<P>(std::make_pair(3ull, 5ull));
  using R = EOU<dv<uint64_t, uint64_t>>;
  assert(std::holds_alternative<typename R::Eou_ret>(r.v()));
  return 0;
}
