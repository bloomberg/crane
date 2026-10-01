#include <local_fix_escapes_by_ref.h>
#include <iostream>
#include <cstring>

using M = LocalFixEscapesByRef;

// Overwrite the stack below the caller, where map_monad_acc's frame was.
[[gnu::noinline]] static void scribble(int depth) {
  volatile unsigned char junk[4096];
  std::memset((void *)junk, 0xA5, sizeof junk);
  if (depth > 0) scribble(depth - 1);
}

[[gnu::noinline]] static M::st<List<uint64_t>> build() {
  crane::fn<M::st<uint64_t>(uint64_t)> f = [](uint64_t x) {
    return M::st<uint64_t>{crane::fn<M::res<uint64_t>(uint64_t)>(
        [x](uint64_t s) { return M::res<uint64_t>::res0(s + 1, 2 * x); })};
  };
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::cons(3, List<uint64_t>::cons(4, List<uint64_t>::nil()))));
  return M::map_monad_acc<uint64_t, uint64_t>(f, l);
}

int main() {
  // The Rocq-level check, where the state function happens to run before
  // the stack is reused.
  bool ok = M::check(std::monostate{});
  // The same computation with map_monad_acc's frame overwritten before the
  // returned state function runs.
  auto m = build();
  scribble(16);
  auto r = m.runst(0);
  const auto &[n, xs] = r;
  uint64_t sum = 0;
  for (const List<uint64_t> *p = &xs; std::holds_alternative<typename List<uint64_t>::Cons>(p->v());) {
    const auto &[h, t] = std::get<typename List<uint64_t>::Cons>(p->v());
    sum += h; p = t.get();
  }
  ok = ok && n == 4 && sum == 20;
  std::cout << (ok ? "ok" : "wrong") << std::endl;
  return ok ? 0 : 1;
}
