#include <c_macro_name.h>

#include <cassert>
#include <variant>

int main() {
  assert(std::holds_alternative<Request::Alloca>(CMacroName::example.v()));
  return 0;
}
