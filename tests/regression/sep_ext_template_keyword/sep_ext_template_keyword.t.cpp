#include "SepExtTemplateKeyword.h"

#include <cassert>

struct IntRaw {
  using elt = int;
  using tree = Datatypes::List<int>;
  static tree empty;
  static Datatypes::List<int> elements(tree t) { return t; }
};
Datatypes::List<int> IntRaw::empty = Datatypes::List<int>::nil();
static_assert(SepExtTemplateKeyword::RawSig<IntRaw>);

int main() {
  using Ops = SepExtTemplateKeyword::MakeOps<IntRaw>;
  auto empty = Datatypes::List<int>::nil();
  assert(Ops::is_empty(empty));

  auto nonempty = Datatypes::List<int>::cons(1, Datatypes::List<int>::nil());
  assert(!Ops::is_empty(nonempty));

  auto elems = Ops::to_list(nonempty);
  assert(!std::holds_alternative<Datatypes::List<int>::Nil>(elems.v()));
  return 0;
}
