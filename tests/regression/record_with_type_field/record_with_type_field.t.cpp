// A record with a [Type] field used as data is demoted from a concept to a
// struct with erased fields,
//   struct alg { std::function<crane::obj(crane::obj, crane::obj)> op; crane::obj unit_; };
// so its literal reaches those fields through the [crane_erase_fn] adapter.

#include <record_with_type_field.h>

#include <cassert>
#include <variant>

/// [nat] is a unary inductive here, so counting the successors is the only way
/// to read it back.
static int to_int(const Nat &n) {
  int k = 0;
  const Nat *p = &n;
  while (const auto *s = std::get_if<Nat::S>(&p->v())) {
    ++k;
    p = s->a0.get();
  }
  return k;
}

int main() {
  assert(to_int(RecordWithTypeField::ex) == 4);
  return 0;
}
