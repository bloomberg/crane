#include <main_toplevel.h>

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
