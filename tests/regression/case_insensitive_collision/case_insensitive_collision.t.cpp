#include <case_insensitive_collision.h>
#include <iostream>
int main() {
  std::cout << CaseInsensitiveCollision::run << std::endl;
  return CaseInsensitiveCollision::run == 7 ? 0 : 1;
}
