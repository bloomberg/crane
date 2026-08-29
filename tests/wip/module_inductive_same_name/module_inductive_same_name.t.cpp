#include <module_inductive_same_name.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = ModuleInductiveSameName::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(1)) {
    std::cout << "expected " << UINT64_C(1) << std::endl;
    return 1;
  }
  return 0;
}
