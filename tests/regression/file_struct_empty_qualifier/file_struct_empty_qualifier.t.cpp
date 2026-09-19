#include "file_struct_empty_qualifier.h"
#include <cassert>

int main() {
  using FSEQ = FileStructEmptyQualifier;
  auto l = List<Nat>::cons(Nat::o(), List<Nat>::cons(Nat::s(Nat::o()),
                                                     List<Nat>::nil()));
  // [a l] is the length of a two-element list, i.e. [Npos (XO XH)].
  N n = FSEQ::a(l);
  assert(std::holds_alternative<N::Npos>(n.v()));
  const Positive &p = std::get<N::Npos>(n.v()).a0;
  assert(std::holds_alternative<Positive::XO>(p.v()));
  assert(std::holds_alternative<Positive::XH>(
      std::get<Positive::XO>(p.v()).a0->v()));
  auto r = FSEQ::b(l);
  assert(r.has_value());
  assert(std::holds_alternative<List<Nat>::Cons>(r.value().v()));
  return 0;
}
