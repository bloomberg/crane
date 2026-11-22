#include <scrutinee_list_return_type.h>

#include <iostream>

int main() {
  auto a = ScrutineeListReturnType::result;
  std::cout << a << std::endl;
  return a == 0 ? 0 : 1;
}
