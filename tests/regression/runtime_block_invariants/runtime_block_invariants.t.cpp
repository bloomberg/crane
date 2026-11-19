#include "runtime_block_invariants.h"
#include "fn.h"
#include "lazy.h"
#include <cassert>
#include <cstdint>
#include <stdexcept>
#include <vector>

static bool throws_logic_error(auto &&f) {
  try {
    f();
  } catch (const std::logic_error &) {
    return true;
  }
  return false;
}

struct alignas(64) wide {
  unsigned char bytes[64];
};

int main() {
  using M = RuntimeBlockInvariants;
  assert(M::hd(M::from(5)) == 5);

  crane::lazy<int> empty;
  assert(throws_logic_error([&] { return empty.force(); }));

  int runs = 0;
  crane::lazy<int> *self = nullptr;
  crane::lazy<int> reentrant(crane::fn<int()>([&]() -> int {
    ++runs;
    return self->force() + 1;
  }));
  self = &reentrant;
  assert(throws_logic_error([&] { return reentrant.force(); }));
  assert(runs == 1);

  // A thunk that throws runs once: every later force rethrows what it threw.
  bool fail = true;
  int tries = 0;
  crane::lazy<int> kept(crane::fn<int()>([&]() -> int {
    ++tries;
    if (fail)
      throw std::runtime_error("not yet");
    return 9;
  }));
  for (int i = 0; i < 2; ++i) {
    try {
      kept.force();
      assert(false);
    } catch (const std::runtime_error &) {
    }
    fail = false;
  }
  assert(tries == 1);

  std::vector<crane::fn<std::uintptr_t()>> fs;
  for (int i = 0; i < 16; ++i) {
    wide w{};
    fs.emplace_back([w] { return reinterpret_cast<std::uintptr_t>(&w); });
  }
  for (auto &f : fs)
    assert(f() % 64 == 0);
  return 0;
}
