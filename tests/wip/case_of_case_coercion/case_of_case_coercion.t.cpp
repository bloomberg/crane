#include <case_of_case_coercion.h>

#include <iostream>

int main() {
  bool a = CaseOfCaseCoercion::ok;
  std::cout << a << std::endl;
  return a ? 0 : 1;
}
