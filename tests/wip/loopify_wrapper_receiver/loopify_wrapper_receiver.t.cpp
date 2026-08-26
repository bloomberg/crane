#include <loopify_wrapper_receiver.h>
#include <iostream>
int main() {
  auto* p = new LoopifyWrapperReceiver::t(LoopifyWrapperReceiver::mk(200000));
  std::cout << "built";
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
