#include <reuse_alias.h>

#include <cassert>
#include <iostream>

int main() {
  using L = ReuseAlias::mylist<unsigned int>;

  // --- double_use ---
  // inc_head and identity on the same list.
  // Correct result: first = [2, 20, 30], second = [1, 20, 30] (unchanged).
  {
    auto l = L::mycons(1u, L::mycons(20u, L::mycons(30u, L::mynil())));
    auto [first, second] = ReuseAlias::double_use(l);

    auto &c1 = std::get<1>(first.v());
    assert(c1.d_a0 == 2u); // inc_head: 1+1 = 2

    auto &c2 = std::get<1>(second.v());
    assert(c2.d_a0 == 1u); // original should still be 1
    std::cout << "double_use: OK" << std::endl;
  }

  // --- double_call ---
  {
    auto l = L::mycons(5u, L::mycons(10u, L::mynil()));
    auto [len_orig, len_inc] = ReuseAlias::double_call(l);
    assert(len_orig == 2u);
    assert(len_inc == 2u);
    std::cout << "double_call: OK" << std::endl;
  }

  // --- alias_and_match ---
  {
    auto l = L::mycons(42u, L::mycons(7u, L::mynil()));
    auto [aliased, val] = ReuseAlias::alias_and_match(l);
    assert(val == 42u);
    auto &c = std::get<1>(aliased.v());
    assert(c.d_a0 == 42u);
    std::cout << "alias_and_match: OK" << std::endl;
  }

  // --- scrutinee_in_branch ---
  {
    auto l = L::mycons(1u, L::mycons(2u, L::mynil()));
    auto [whole, tail] = ReuseAlias::scrutinee_in_branch(l);
    auto &w = std::get<1>(whole.v());
    assert(w.d_a0 == 1u);
    auto &t = std::get<1>(tail.v());
    assert(t.d_a0 == 2u);
    std::cout << "scrutinee_in_branch: OK" << std::endl;
  }

  // --- triple_inc ---
  {
    auto l = L::mycons(10u, L::mycons(20u, L::mynil()));
    auto result = ReuseAlias::triple_inc(l);
    auto &c = std::get<1>(result.v());
    assert(c.d_a0 == 13u); // 10 + 3
    std::cout << "triple_inc: OK" << std::endl;
  }

  return 0;
}
