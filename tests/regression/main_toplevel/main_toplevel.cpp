#include <main_toplevel.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

void Greeter::greet() {
  std::cout << "hello from toplevel main"s << '\n';
  return;
}

int main() {
  {
    Greeter::greet();
    return 0;
  }
}
