#include <erased_type_field_lambda.h>
#include <iostream>
int main() {
  std::cout << ErasedTypeFieldLambda::run << std::endl;
  return ErasedTypeFieldLambda::run == 24 ? 0 : 1;
}
