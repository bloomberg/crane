// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <same_named_file_modules.h>
#include <cassert>
#include <cstdint>

int main() {
  assert(SameNamedFileModules::found == 2);
  assert(SameNamedFileModules::larger);
  // The machine of the view's recursor holds the index it passes on by
  // pointer, into the view: 2^14 - 1 has 16382 successor steps.
  {
    Positive p = Positive::xh();
    for (int i = 0; i < 13; ++i) p = Positive::xi(std::move(p));
    Coq_Pos::PeanoView v = Coq_Pos::peanoView(p);
    std::uint64_t steps = v.PeanoView_rect<std::uint64_t>(
        0, [](const Positive &, const Coq_Pos::PeanoView &, std::uint64_t r) { return r + 1; }, p);
    assert(steps == 16382);
  }
  return 0;
}
