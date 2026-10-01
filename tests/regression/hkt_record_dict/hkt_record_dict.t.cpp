// A higher-kinded signature written as a Record rather than a Class.
//
// The record is a value dictionary: its parameter is the carrier already
// applied at the erased element ([FnD<std::optional<crane::obj>>]), its field
// is projected off the value, and the accessor converts the carrier back to
// the element the caller means.

#include <hkt_record_dict.h>

#include <cassert>

static int to_int(Nat n) {
  int i = 0;
  while (std::holds_alternative<Nat::S>(n.v())) {
    n = *std::get<Nat::S>(n.v()).a0;
    ++i;
  }
  return i;
}

int main() {
  assert(HktRecordDict::ex.has_value());
  assert(to_int(*HktRecordDict::ex) == 2);
  return 0;
}
