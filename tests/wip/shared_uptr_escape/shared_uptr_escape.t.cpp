#include <shared_uptr_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using SUE = SharedUptrEscape;

  // conditional_share flag=0: identity(t).tree_sum() = 60
  auto r1 = SUE::conditional_share(0u);
  std::cout << "conditional_share(0) = " << r1 << std::endl;
  assert(r1 == 60u);

  // conditional_share flag=1: dup(t) → (t, t), sum both = 120
  // BUG: dup() returns std::make_pair(this, this) which tries to
  // construct shared_ptr<tree> from raw const tree* → compile error
  // (and would be double-free if it compiled)
  auto r2 = SUE::conditional_share(1u);
  std::cout << "conditional_share(1) = " << r2 << std::endl;
  assert(r2 == 120u);

  // use_extracted_twice: extract subtree, use shared_ptr twice
  // Expected: 10 + 10 = 20
  auto r3 = SUE::use_extracted_twice;
  std::cout << "use_extracted_twice = " << r3 << std::endl;
  assert(r3 == 20u);

  // unwrap_and_dup: wrap in constructor, unwrap, use twice
  // Expected: 42 + 42 = 84
  auto r4 = SUE::unwrap_and_dup;
  std::cout << "unwrap_and_dup = " << r4 << std::endl;
  assert(r4 == 84u);

  std::cout << "All shared_uptr_escape tests passed!" << std::endl;
  return 0;
}
