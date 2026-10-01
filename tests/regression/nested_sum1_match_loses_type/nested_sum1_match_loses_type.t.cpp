#include <nested_sum1_match_loses_type.h>

#include <cassert>

int main() {
  auto r = NestedSum1MatchLosesType::run;
  assert(r.has_value());
  return 0;
}
