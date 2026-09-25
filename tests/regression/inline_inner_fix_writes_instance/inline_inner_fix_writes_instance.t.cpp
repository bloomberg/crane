#include <cassert>
#include <inline_inner_fix_writes_instance.h>

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
  auto r = InlineInnerFixWritesInstance::use<P>(std::make_pair(3ull, 5ull));
  assert(r.has_value());
  assert(r.value().first == 3);
  return 0;
}
