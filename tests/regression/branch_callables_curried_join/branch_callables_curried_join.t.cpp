// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <branch_callables_curried_join.h>

#include <cstdint>
#include <iostream>

#define M BranchCallablesCurriedJoin

int main() {
  int fails = 0;
  auto e = List<uint64_t>::nil();
  auto one = List<uint64_t>::cons(1, List<uint64_t>::nil());
  if (!(M::t(e) == 1)) { std::cout << "FAIL: M::t(e)" << std::endl; ++fails; }
  if (!(M::t(one) == 2)) { std::cout << "FAIL: M::t(one)" << std::endl; ++fails; }
  auto zero_one = List<uint64_t>::cons(0, one);
  if (!(M::t2(e) == 7)) { std::cout << "FAIL: M::t2(e)" << std::endl; ++fails; }
  if (!(M::t2(one) == 7)) { std::cout << "FAIL: M::t2(one)" << std::endl; ++fails; }
  if (!(M::t2(zero_one) == 0)) { std::cout << "FAIL: M::t2(zero_one)" << std::endl; ++fails; }
  if (!(M::v1 == 0)) { std::cout << "FAIL: M::v1" << std::endl; ++fails; }
  if (!(M::v2 == 0)) { std::cout << "FAIL: M::v2" << std::endl; ++fails; }
  if (!(M::v3(std::nullopt) == 0)) { std::cout << "FAIL: M::v3(None)" << std::endl; ++fails; }
  if (!(M::v3(std::optional<uint64_t>(4)) == 4)) { std::cout << "FAIL: M::v3(Some 4)" << std::endl; ++fails; }
  if (!(M::v4 == 0)) { std::cout << "FAIL: M::v4" << std::endl; ++fails; }
  if (!(M::v5 == 1)) { std::cout << "FAIL: M::v5" << std::endl; ++fails; }
  if (!(M::v11(e) == 1)) { std::cout << "FAIL: M::v11(e)" << std::endl; ++fails; }
  if (!(M::v11(one) == 2)) { std::cout << "FAIL: M::v11(one)" << std::endl; ++fails; }
  if (!(M::v12(e) == 2)) { std::cout << "FAIL: M::v12(e)" << std::endl; ++fails; }
  if (!(M::v12(one) == 1)) { std::cout << "FAIL: M::v12(one)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All branch_callables_curried_join tests passed!" << std::endl;
  return fails;
}
