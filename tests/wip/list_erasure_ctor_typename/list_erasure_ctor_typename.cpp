#include "list_erasure_ctor_typename.h"

/// WIP: Using `nth_error` on a `list (nat -> nat)` emits the erasure-converting
/// `List` constructor with a doubled qualifier
/// (`typename List::typename List::template list<_U>::Nil`), which is not even
/// syntactically valid C++.
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
