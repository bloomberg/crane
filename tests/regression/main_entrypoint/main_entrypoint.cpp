#include <main_entrypoint.h>

void MainEntrypoint::main() {
  std::cout << "hello from main"s << '\n';
  return;
}

int main() {
  MainEntrypoint::main();
  return 0;
}
