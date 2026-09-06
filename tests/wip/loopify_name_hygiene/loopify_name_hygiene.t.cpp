#include <loopify_name_hygiene.h>
#include <iostream>
int main() {
  std::cout << LoopifyNameHygiene::run << std::endl;
  return LoopifyNameHygiene::run == 22 ? 0 : 1;
}
