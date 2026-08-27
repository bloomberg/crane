#include "list_erasure_ctor_typename.h"

/// Using nth_error on a list (nat -> nat) instantiates the
/// erasure-converting List constructor, whose body names the source
/// instantiation's constructor structs.  Because list is not merged into
/// its List wrapper struct, those names are dependent and must be spelled
/// typename List::template list<_U>::Nil.
std::optional<std::function<uint64_t(uint64_t)>>
ListErasureCtorTypename::pick(uint64_t n) {
  return List::template nth_error<std::function<uint64_t(uint64_t)>>(
      List::template list<std::function<uint64_t(uint64_t)>>::cons(
          [](uint64_t k) { return (k + UINT64_C(1)); },
          List::template list<std::function<uint64_t(uint64_t)>>::cons(
              [](uint64_t k) { return (k * UINT64_C(2)); },
              List::template list<std::function<uint64_t(uint64_t)>>::nil())),
      n);
}
