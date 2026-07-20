// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression for the reified ITree runtime invariants (crane_itree.h):
//   * factories reject null Tau next / null Vis effect+continuation (finding 132)
//   * a Ret tree can be run more than once without corruption (finding 37)
//   * ITree<void>::run keeps the node alive via shared ownership (finding 86):
//     an effect that drops every other owner must not free the running node.

#include "itree_invariants.h"

#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>

int main() {
  // finding 132: null Tau next rejected.
  {
    bool threw = false;
    try {
      ITree<int>::tau(nullptr);
    } catch (const std::invalid_argument &) {
      threw = true;
    }
    assert(threw);
  }

  // finding 132: null Vis continuation rejected.
  {
    bool threw = false;
    try {
      ITree<int>::vis([]() -> std::any { return std::any{}; },
                      std::function<std::shared_ptr<ITree<int>>(std::any)>());
    } catch (const std::invalid_argument &) {
      threw = true;
    }
    assert(threw);
  }

  // finding 37: a Ret tree is re-runnable (payload copied, not moved out).
  {
    auto t = ITree<int>::ret(7);
    assert(t->run() == 7);
    assert(t->run() == 7);
  }

  // finding 86: a void effect that drops the last external owner must not free
  // the node out from under run().  The tree owns itself only through [holder]
  // here; the effect clears [holder], leaving run()'s own shared_from_this
  // reference as the sole keeper.
  {
    auto holder = std::make_shared<std::shared_ptr<ITree<void>>>();
    *holder = ITree<void>::vis(
        [holder]() -> std::any {
          *holder = nullptr; // drop the external owner mid-run
          return std::any{};
        },
        [](std::any) { return ITree<void>::ret(); });
    (*holder)->run();
  }

  std::cout << "All itree_invariants tests passed!" << std::endl;
  return 0;
}
