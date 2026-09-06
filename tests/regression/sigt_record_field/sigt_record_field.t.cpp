#include <sigt_record_field.h>
#include <iostream>
int main() {
  std::cout << SigtRecordField::run << std::endl;
  return SigtRecordField::run == 3 ? 0 : 1;
}
