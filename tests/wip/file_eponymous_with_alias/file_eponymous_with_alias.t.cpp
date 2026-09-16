#include <file_eponymous_with_alias.h>

#include <cassert>
#include <variant>

int main() {
  // append empty empty [1] = [1]
  assert(std::holds_alternative<List<Nat>::Cons>(FileEponymousWithAlias::use.v()));
  return 0;
}
