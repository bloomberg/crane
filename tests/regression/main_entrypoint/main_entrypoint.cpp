#include <main_entrypoint.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>
#include <variant>

void MainEntrypoint::main() {
  std::cout << "hello from main"s << '\n';
  return;
}

int main() {
  MainEntrypoint::main();
  return 0;
}
