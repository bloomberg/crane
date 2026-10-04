#include "main_toplevel.h"

void Greeter::greet() {
  std::cout << std::string("hello from toplevel main") << '\n';
  return;
}

int main() {
  {
    Greeter::greet();
    return 0;
  }
}
