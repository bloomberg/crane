#include <loopify_nested_calls.h>

#include <cassert>
#include <cstdint>
#include <iostream>

// Shape 1: sum_signum n = number of nonzero naturals in [1..n]
// sum_signum 0 = 0
// sum_signum 1 = 0  (n'=0, here=0)
// sum_signum 2 = 1  (n'=1, here=1)
// sum_signum 3 = 2  (n'=2, here=1; plus sum_signum 2 = 1)
static void test_sum_signum() {
  assert(sum_signum(0ull) == 0ull);
  assert(sum_signum(1ull) == 0ull);
  assert(sum_signum(2ull) == 1ull);
  assert(sum_signum(3ull) == 2ull);
  std::cout << "sum_signum: OK" << std::endl;
}

// Shape 2: down_let n = [n-1, n-2, ..., 0]
static void test_down_let() {
  auto l = down_let(3ull);
  const List<uint64_t> *cur = &l;
  uint64_t expected[] = {2ull, 1ull, 0ull};
  for (uint64_t v : expected) {
    assert(std::holds_alternative<typename List<uint64_t>::Cons>(cur->v()));
    const auto &cell = std::get<typename List<uint64_t>::Cons>(cur->v());
    assert(cell.a == v);
    cur = cell.l.get();
  }
  assert(std::holds_alternative<typename List<uint64_t>::Nil>(cur->v()));
  std::cout << "down_let: OK" << std::endl;
}

// Shape 3: down_inline n = [n-1, n-2, ..., 0]
static void test_down_inline() {
  auto l = down_inline(3ull);
  const List<uint64_t> *cur = &l;
  uint64_t expected[] = {2ull, 1ull, 0ull};
  for (uint64_t v : expected) {
    assert(std::holds_alternative<typename List<uint64_t>::Cons>(cur->v()));
    const auto &cell = std::get<typename List<uint64_t>::Cons>(cur->v());
    assert(cell.a == v);
    cur = cell.l.get();
  }
  assert(std::holds_alternative<typename List<uint64_t>::Nil>(cur->v()));
  std::cout << "down_inline: OK" << std::endl;
}

int main() {
  test_sum_signum();
  test_down_let();
  test_down_inline();
  return 0;
}
