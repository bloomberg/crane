#include <cassert>
#include <rank3_handler.h>

namespace {

/// The [nat] a handler-of-rank-three round trip came back with.
int to_int(const Nat &n) {
  int acc = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    ++acc;
    cur = std::get<Nat::S>(cur->v()).a0.get();
  }
  return acc;
}

} // namespace

int main() {
  assert(std::holds_alternative<Option<Nat>::Some>(top.v()));
  assert(to_int(std::get<Option<Nat>::Some>(top.v()).a) == 7);

  // The same handler, applied at two types by a rank-2 consumer.
  const Option<Nat> twice =
      useTwice([]<typename X>(const ReqA<X> &a) { return Option<X>::some(a.a0); });
  assert(to_int(std::get<Option<Nat>::Some>(twice.v()).a) == 7);

  // Rank three from the C++ side: a consumer handed the handler that
  // [runWith2] builds, applied at a type the consumer picks.
  const Option<Bool0> b =
      runWith2([](auto &&f) { return f(ReqA<Bool0>::mka(Bool0::TRUE_)); });
  assert(std::get<Option<Bool0>::Some>(b.v()).a == Bool0::TRUE_);

  return 0;
}
