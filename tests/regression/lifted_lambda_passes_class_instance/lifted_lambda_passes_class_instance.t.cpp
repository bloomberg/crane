#include <cassert>
#include <lifted_lambda_passes_class_instance.h>

int main() {
  const auto &r = LiftedLambdaPassesClassInstance::run;
  assert(std::holds_alternative<typename Nat::S>(r.a0.v()));
  return 0;
}
