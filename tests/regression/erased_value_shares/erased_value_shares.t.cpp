#define CRANE_ALLOC_PROFILE
#include <alloc_profile.h>
#include <erased_value_shares.h>

#include <cassert>
#include <iostream>
#include <type_traits>

using E = ErasedValueShares;

static uint64_t length(const List<uint64_t> &l) {
  uint64_t n = 0;
  for (const List<uint64_t> *p = &l;
       std::holds_alternative<typename List<uint64_t>::Cons>(p->v());
       p = std::get<typename List<uint64_t>::Cons>(p->v()).l.get())
    ++n;
  return n;
}

int main() {
  const crane::obj &box = E::packed.a1;
  static_assert(std::is_same_v<std::decay_t<decltype(E::packed.a1)>, crane::obj>,
                "the payload is erased");
  // Read in place: a reference into the box, not a copy of the list.
  const List<uint64_t> &l = crane::any_cast<List<uint64_t>>(box);
  assert(&l == &crane::any_cast<List<uint64_t>>(box));
  assert(length(l) == 1000u);

  auto &stats = crane::alloc_profile_stats();
  const auto before = stats.news.load();
  uint64_t live = 0;
  for (int i = 0; i < 1000000; ++i) {
    crane::obj copy = box;          // a count bump, never a deep copy
    auto pair = E::packed;          // copying the record copies a handle
    live += copy.has_value() && pair.a1.has_value();
  }
  const auto after = stats.news.load();
  std::cout << "allocations while copying 10^6 times: " << (after - before)
            << std::endl;
  assert(after == before);
  assert(live == 1000000u);

  // Every copy reads the one list.
  crane::obj copy = box;
  assert(&crane::any_cast<List<uint64_t>>(copy) == &l);

  // The wrong type is still an error.
  bool threw = false;
  try {
    (void)crane::any_cast<uint64_t>(box);
  } catch (const std::bad_any_cast &) {
    threw = true;
  }
  assert(threw);

  std::cout << "All erased_value_shares tests passed!" << std::endl;
  return 0;
}
