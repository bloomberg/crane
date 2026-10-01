#include <loopify_frame_lambda_type.h>
#include <iostream>
int main() {
  bool ok = LoopifyFrameLambdaType::check(std::monostate{});
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
