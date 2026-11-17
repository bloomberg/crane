#include <custom_match_lambda_scrutinee.h>

#include <cassert>
#include <iostream>

int main() {
  assert(CustomMatchLambdaScrutinee::same_i);
  assert(!CustomMatchLambdaScrutinee::diff_i);
  assert(!CustomMatchLambdaScrutinee::diff_ctor);
  assert(CustomMatchLambdaScrutinee::same_fp);
  assert(!CustomMatchLambdaScrutinee::diff_fp);
  std::cout << "custom_match_lambda_scrutinee: ok" << std::endl;
  return 0;
}
