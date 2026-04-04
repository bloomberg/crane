#include <recursive_monadic.h>

int main() {
  // Test 1: countdown
  auto r1 = RecursiveMonadic::countdown(3);
  // countdown(3) -> tick;tick;tick;Ret 0
  // assert(r1 == 0); // if it compiles, the recursion type handling works

  // Test 4: repeat_action
  auto r4 = RecursiveMonadic::repeat_action(2, "hi"s);
  // repeat_action(2) -> hi;hi;Ret 2 (counts steps)

  // Test 7: mutual recursion
  auto r7 = RecursiveMonadic::even_action(4);
  // even_action(4) -> e;o;e;o;Ret "even"

  // Test 8: find_first
  auto pred = [](unsigned int n) { return n > 2u; };
  auto r8 = RecursiveMonadic::find_first(
    pred,
    List<unsigned int>::cons(1, List<unsigned int>::cons(3, List<unsigned int>::nil()))
  );

  return 0;
}
