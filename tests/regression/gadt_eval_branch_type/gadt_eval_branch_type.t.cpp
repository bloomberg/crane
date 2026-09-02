#include <gadt_eval_branch_type.h>
#include <cassert>

int main() {
  auto p = GadtEvalBranchType::run;
  assert(p.second == true);
  return 0;
}
