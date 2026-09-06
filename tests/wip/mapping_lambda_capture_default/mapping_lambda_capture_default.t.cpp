#include <mapping_lambda_capture_default.h>
#include <iostream>
int main() {
  std::cout << MappingLambdaCaptureDefault::run << std::endl;
  return MappingLambdaCaptureDefault::run == -39 ? 0 : 1;
}
