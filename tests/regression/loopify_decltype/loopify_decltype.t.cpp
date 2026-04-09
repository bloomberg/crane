#include <loopify_decltype.h>

#include <cassert>
#include <iostream>

int main() {
  using LD = LoopifyDecltype;

  // count_true([true, false, true, true])  =  3
  auto bools = List<bool>::cons(
      true,
      List<bool>::cons(
          false, List<bool>::cons(true, List<bool>::cons(true, List<bool>::nil()))));
  assert(LD::count_true(bools) == 3u);
  std::cout << "count_true ok" << std::endl;

  // sum_flagged([{true,10}, {false,99}, {true,5}])  =  15
  auto items = List<std::shared_ptr<LD::item>>::cons(
      std::make_shared<LD::item>(LD::item{true, 10u}),
      List<std::shared_ptr<LD::item>>::cons(
          std::make_shared<LD::item>(LD::item{false, 99u}),
          List<std::shared_ptr<LD::item>>::cons(
              std::make_shared<LD::item>(LD::item{true, 5u}),
              List<std::shared_ptr<LD::item>>::nil())));
  assert(LD::sum_flagged(items) == 15u);
  std::cout << "sum_flagged ok" << std::endl;

  std::cout << "All loopify_decltype tests passed!" << std::endl;
  return 0;
}
