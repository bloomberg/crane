#include "main_entrypoint.h"

void MainEntrypoint::main() {
  std::cout << std::string("hello from main") << '\n';
}

int main() {
  MainEntrypoint::main();
  return 0;
}
