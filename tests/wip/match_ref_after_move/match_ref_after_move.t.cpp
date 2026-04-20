#include <match_ref_after_move.h>

#include <cassert>
#include <iostream>

int main() {
  using MRAM = MatchRefAfterMove;

  // test1: head_and_tail_length [10,20,30] = (10, 2), sum = 12
  auto r1 = MRAM::test1;
  std::cout << "test1 = " << r1 << " (expected 12)" << std::endl;
  assert(r1 == 12u);

  // test2: nested_match_probe [10,20,30] = 10+20+1 = 31
  auto r2 = MRAM::test2;
  std::cout << "test2 = " << r2 << " (expected 31)" << std::endl;
  assert(r2 == 31u);

  // test3: match_into_pair [5,10] = (5, [6,10])
  // = 5 + mylist_sum [6,10] = 5 + 16 = 21
  auto r3 = MRAM::test3;
  std::cout << "test3 = " << r3 << " (expected 21)" << std::endl;
  assert(r3 == 21u);

  // test4: double_match [7,8,9] = (7, [8,9])
  // = 7 + mylist_sum [8,9] = 7 + 17 = 24
  auto r4 = MRAM::test4;
  std::cout << "test4 = " << r4 << " (expected 24)" << std::endl;
  assert(r4 == 24u);

  // test5: match_with_cont [100,200,300] (+) = 100 + 2 = 102
  auto r5 = MRAM::test5;
  std::cout << "test5 = " << r5 << " (expected 102)" << std::endl;
  assert(r5 == 102u);

  // test6: complex_match (Right [50,60]) = 50 + 1 = 51
  auto r6 = MRAM::test6;
  std::cout << "test6 = " << r6 << " (expected 51)" << std::endl;
  assert(r6 == 51u);

  std::cout << "All match_ref_after_move tests passed!" << std::endl;
  return 0;
}
