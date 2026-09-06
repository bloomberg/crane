#include <module_local_return_type.h>
#include <iostream>
int main() {
  std::cout << ModuleLocalReturnType::run << std::endl;
  return ModuleLocalReturnType::run == 4 ? 0 : 1;
}
