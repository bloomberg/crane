#include <string_cat_max_length.h>

#include <iostream>

int main() {
  bool a = StringCatMaxLength::clamped;
  bool b = StringCatMaxLength::big_clamped;
  std::cout << a << " " << b << std::endl;
  return (a && b) ? 0 : 1;
}
