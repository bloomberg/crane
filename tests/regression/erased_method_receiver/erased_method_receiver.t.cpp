// An erased value used as a method receiver: [projT2 s] has C++ type
// [crane::obj] and is handed to [.length()], so it has to be recovered at the
// parameter's type first.

#include <erased_method_receiver.h>

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
  assert(to_int(ErasedMethodReceiver::run) == 1);
  return 0;
}
