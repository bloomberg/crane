#include <loopify_continue_moves_local.h>

#include <cassert>
#include <iostream>

int main() {
  using L = LoopifyContinueMovesLocal;

  // count_down 3 [] = [0; 1; 2]
  const auto &d = L::test_count_down;
  assert(d.length() == 3u);

  // count_both 3 [] 0: lengths 1, 2, 3 summed.
  assert(L::test_count_both.first.length() == 3u);
  assert(L::test_count_both.second == 6u);

  // split_off 3 [] []: the last turn's tail is the list without its head.
  assert(L::test_split_off.first.length() == 3u);
  assert(L::test_split_off.second.length() == 2u);

  // peel 3 [] []: as split_off.
  assert(L::test_peel.first.length() == 3u);
  assert(L::test_peel.second.length() == 2u);

  std::cout << "All loopify_continue_moves_local tests passed!" << std::endl;
  return 0;
}
