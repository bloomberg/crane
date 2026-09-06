#include <class_method_function_payload.h>
#include <iostream>
int main() {
  std::cout << ClassMethodFunctionPayload::run << std::endl;
  return ClassMethodFunctionPayload::run == 9 ? 0 : 1;
}
