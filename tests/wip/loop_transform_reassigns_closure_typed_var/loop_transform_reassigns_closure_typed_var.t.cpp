#include <loop_transform_reassigns_closure_typed_var.h>

#include <cassert>
#include <vector>

namespace {

int to_int(const Nat &n) {
  int acc = 0;
  const Nat *cur = &n;
  while (const auto *s = std::get_if<Nat::S>(&cur->v())) {
    ++acc;
    cur = s->a0.get();
  }
  return acc;
}

std::vector<int> to_vector(const Lst<Nat> &l) {
  std::vector<int> out;
  const Lst<Nat> *cur = &l;
  while (const auto *c = std::get_if<Lst<Nat>::Cons>(&cur->v())) {
    out.push_back(to_int(c->x));
    cur = c->xs.get();
  }
  return out;
}

} // namespace

int main() {
  // [1; 2] mapped with (+ 3).  The callable is rebuilt once per element, so
  // the shadow variable holding it is reassigned across the loop's back edge.
  assert((to_vector(run(std::monostate{})) == std::vector<int>{4, 5}));
  return 0;
}
