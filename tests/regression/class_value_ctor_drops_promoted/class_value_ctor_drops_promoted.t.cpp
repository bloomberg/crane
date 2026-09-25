#include <class_value_ctor_drops_promoted.h>

#include <cassert>

int main() {
  auto d = ClassValueCtorDropsPromoted::run;
  (void)d;
  return 0;
}
