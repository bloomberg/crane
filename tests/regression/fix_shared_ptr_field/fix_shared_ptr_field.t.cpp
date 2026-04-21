#include <fix_shared_ptr_field.h>

#include <cassert>
#include <iostream>

int main() {
  using FSPF = FixSharedPtrField;

  // test1: l=[10,20,30], h=10, t=[20,30], mylist_sum(t)=50.
  //        compute(5) = (10+50) + 5 = 65.
  // BUG: fixpoint captures d_a0 (unsigned int) and d_a1 (shared_ptr<mylist>)
  // by [&]. After make_list_fn returns, both dangle.
  // d_a1->mylist_sum() dereferences freed heap memory.
  auto r1 = FSPF::test1;
  std::cout << "test1 = " << r1 << " (expected 65)" << std::endl;
  assert(r1 == 65u);

  // test2: l=[100,200], h=100, mylist_sum(t)=200, compute(0)=300.
  auto r2 = FSPF::test2;
  std::cout << "test2 = " << r2 << " (expected 300)" << std::endl;
  assert(r2 == 300u);

  // test3: l=[5,10,15,20,25], h=5, mylist_sum(t)=70, compute(10)=85.
  auto r3 = FSPF::test3;
  std::cout << "test3 = " << r3 << " (expected 85)" << std::endl;
  assert(r3 == 85u);

  std::cout << "All fix_shared_ptr_field tests passed!" << std::endl;
  return 0;
}
