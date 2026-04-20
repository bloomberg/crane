#include <existential_closure_probe.h>

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Pack a closure into a type-erased wrapper.
std::shared_ptr<ExistentialClosureProbe::wrap>
ExistentialClosureProbe::pack_fn(const unsigned int base) {
  return wrap::wrap0([=](const unsigned int x) mutable { return (x + base); });
}

/// Unpack and apply.
__attribute__((pure)) unsigned int ExistentialClosureProbe::apply_packed(
    const std::shared_ptr<ExistentialClosureProbe::wrap> &_x0,
    const unsigned int _x1) {
  return unwrap<std::function<unsigned int(unsigned int)>>(_x0)(_x1);
}

/// Store a closure that captures another closure.
std::shared_ptr<ExistentialClosureProbe::wrap>
ExistentialClosureProbe::pack_composed(const unsigned int a,
                                       const unsigned int b) {
  std::function<unsigned int(unsigned int)> f =
      [=](const unsigned int x) mutable { return (x + a); };
  std::function<unsigned int(unsigned int)> g =
      [=](const unsigned int x) mutable { return (f(x) * b); };
  return wrap::wrap0(g);
}
