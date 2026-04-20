#include <fix_chain_build.h>

#include <functional>
#include <type_traits>
#include <utility>

/// Recursive construction of a closure chain. Each level creates a
/// local fixpoint that captures the current n AND the previous
/// level's closure prev, then stores the fixpoint in a pair with
/// its base value (preventing uncurrying).
///
/// BUG: Each step fixpoint uses & capture, binding n (the
/// current stack frame's parameter), prev (a local variable),
/// and step itself. When build_chain returns, the stack frame
/// is destroyed, and the returned closure holds dangling references.
__attribute__((pure))
std::pair<unsigned int, std::function<unsigned int(unsigned int)>>
FixChainBuild::build_chain(const unsigned int n) {
  if (n <= 0) {
    return std::make_pair(0u, [](const unsigned int x) { return x; });
  } else {
    unsigned int n_ = n - 1;
    auto _cs = build_chain(n_);
    const unsigned int &_x = _cs.first;
    const std::function<unsigned int(unsigned int)> &prev = _cs.second;
    std::function<unsigned int(unsigned int)> step;
    step = [&](unsigned int x) -> unsigned int {
      if (x <= 0) {
        return n;
      } else {
        unsigned int x_ = x - 1;
        return (prev(step(x_)) + 1);
      }
    };
    return std::make_pair(n, step);
  }
}
