// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <known_list_scrutinee_erased.h>

#include <cstdint>
#include <iostream>

#define M KnownListScrutineeErased

int main() {
  int fails = 0;
  if (!(M::t == std::optional<uint64_t>(5))) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All known_list_scrutinee_erased tests passed!" << std::endl;
  return fails;
}
