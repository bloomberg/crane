// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <case_of_case_result_type.h>

#include <cstdint>
#include <iostream>

#define M CaseOfCaseResultType

int main() {
  int fails = 0;
  if (!(M::t == 8)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::g(3, 4) == true)) { std::cout << "FAIL: M::g(3, 4)" << std::endl; ++fails; }
  if (!(M::g(3, 0) == false)) { std::cout << "FAIL: M::g(3, 0)" << std::endl; ++fails; }
  if (!(M::u == 12)) { std::cout << "FAIL: M::u" << std::endl; ++fails; }

  if (!(M::v == 3)) { std::cout << "FAIL: M::v" << std::endl; ++fails; }
  if (fails == 0) std::cout << "All case_of_case_result_type tests passed!" << std::endl;
  return fails;
}
