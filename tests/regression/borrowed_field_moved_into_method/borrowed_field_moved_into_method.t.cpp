#include <borrowed_field_moved_into_method.h>
#include <iostream>
int main() {
  bool ok = BorrowedFieldMovedIntoMethod::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
