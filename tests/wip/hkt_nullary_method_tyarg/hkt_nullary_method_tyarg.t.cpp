#include <hkt_nullary_method_tyarg.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(HktNullaryMethodTyarg::run.v()));
  return 0;
}
