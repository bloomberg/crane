#include <name_matches_module.h>
#include <iostream>
int main() {
  std::cout << NameMatchesModule::run << std::endl;
  return NameMatchesModule::run == 10 ? 0 : 1;
}
