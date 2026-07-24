#include <action_container_cast.h>

#include <iostream>

// Reproduction driver. The defect lives in the generated header: the semantic
// ACTION for [NVal -> NT NArr] (the JList/JAssoc shape) must convert the erased
// std::deque<std::any> produced by NArr's nil action into RArr's concrete
// std::deque<R>. It uses a plain any_cast instead of crane_container_cast (the
// predicate path uses crane_container_cast correctly).
//
// In the real extracted JSON parser this compiles but throws std::bad_any_cast
// at runtime on every array/object (e.g. "[]"). In this minimal repro the same
// defective action conversion is ill-typed, so merely referencing `entries`
// fails to compile -- either way it pinpoints the same missing container cast.
int main() {
  std::cout << "entries size = " << entries.size() << std::endl;
  return 0;
}
