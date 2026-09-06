#include <let_polymorphic_fun.h>
#include <iostream>
int main() {
  std::cout << LetPolymorphicFun::run << std::endl;
  return LetPolymorphicFun::run == 5 ? 0 : 1;
}
