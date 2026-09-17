#include <lifted_instance_qualified.h>

#include <cassert>

/// Rocq's [string] is a list of characters, so it is extracted as one.
static int length(const String &s) {
  int n = 0;
  for (const String *p = &s;
       std::holds_alternative<String::String0>(p->v());
       p = std::get<String::String0>(p->v()).a1.get()) {
    ++n;
  }
  return n;
}

int main() {
  // "o" ++ "u" ++ "n"
  assert(length(LiftedInstanceQualified::use(Nat::o())) == 3);
  return 0;
}
