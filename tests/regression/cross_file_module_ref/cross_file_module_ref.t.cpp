#include <cross_file_module_ref.h>

#include <cassert>
#include <variant>

static unsigned to_uint(const Nat &n) {
  unsigned c = 0;
  const Nat *p = &n;
  while (std::holds_alternative<Nat::S>(p->v())) {
    ++c;
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return c;
}

int main() {
  // Lib3.M.twice Lib.bump 0 = 2, plus Lib2.bump 0 = 2.
  assert(to_uint(CrossFileModuleRef::use) == 4);
  return 0;
}
