#include "main_entrypoint.h"

void MainEntrypoint::main() {
  std::cout << std::string("hello from main") << '\n';
  return;
}

int main() {
  MainEntrypoint::main();
  return 0;
}
