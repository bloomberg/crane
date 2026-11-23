#include <bake_prim_string.h>

#include <iostream>
#include <string>

int main() {
  std::string g = BakePrimString::greeting;
  std::string f = BakePrimString::first_word;
  std::cout << g << " " << f << std::endl;
  return (g == "abcd" && f == "ab") ? 0 : 1;
}
