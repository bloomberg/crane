#define CRANE_ALLOC_PROFILE
#include <alloc_profile.h>
#include <closure_copy_shares.h>

#include <cassert>
#include <iostream>
#include <type_traits>
#include <variant>

int main() {
  using C = ClosureCopyShares;
  using Fs = std::decay_t<decltype(C::closures)>;

  // The second closure captures closures that capture closures, down to one
  // capturing a list.
  const auto &cell0 = std::get<typename Fs::Cons>(C::closures.v());
  const auto &cell1 = std::get<typename Fs::Cons>(cell0.l->v());
  auto f = cell1.a;
  static_assert(crane::is_fn<decltype(f)>::value,
                "a Rocq function value is a crane::fn");
  // 36 + S (36 + x)
  assert(f(0u) == 73u);

  auto &stats = crane::alloc_profile_stats();
  const auto before = stats.news.load();
  unsigned long long live = 0;
  for (int i = 0; i < 1000000; ++i) {
    auto copy = f;             // a count bump, never a clone
    decltype(f) other(copy);
    live += other ? 1u : 0u;
  }
  const auto after = stats.news.load();
  std::cout << "allocations while copying 10^6 times: " << (after - before)
            << std::endl;
  assert(after == before);
  assert(live == 1000000u);

  // Every copy shares the one closure, and a call leaves its captures intact
  // for the next.
  auto g = f;
  assert(g(0u) == 73u);
  assert(f(1u) == 74u);
  assert(g(2u) == 75u);

  std::cout << "All closure_copy_shares tests passed!" << std::endl;
  return 0;
}
