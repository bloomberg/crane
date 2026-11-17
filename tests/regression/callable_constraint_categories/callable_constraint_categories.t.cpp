// A callable parameter's constraint names the operands the body really passes:
// map hands its callback a borrowed element (const T1 &), curry a temporary
// pair (a prvalue), foldl a moved accumulator (T2 &&).  A callback the body
// could not call is rejected by the constraint, and one it can call is not.
#include "callable_constraint_categories.h"

#include <cassert>
#include <utility>

using L = CallableConstraintCategories::lst<int>;
using P = std::pair<int, int>;

template <class F>
constexpr bool map_accepts =
    requires(F f, const L &l) { CallableOps::map<int, int>(f, l); };
template <class F>
constexpr bool curry_accepts =
    requires(F f) { CallableConstraintCategories::curry<int, int, int>(f, 1, 2); };
template <class F>
constexpr bool foldl_accepts =
    requires(F f, const L &l) { CallableOps::foldl<int, int>(f, 0, l); };

static_assert(map_accepts<int (*)(const int &)>);
static_assert(map_accepts<int (*)(int)>);
static_assert(!map_accepts<int (*)(int &)>);

static_assert(curry_accepts<int (*)(P &&)>);
static_assert(curry_accepts<int (*)(P)>);
static_assert(curry_accepts<int (*)(const P &)>);
static_assert(!curry_accepts<int (*)(P &)>);

static_assert(foldl_accepts<int (*)(int &&, const int &)>);
static_assert(foldl_accepts<int (*)(int, int)>);
static_assert(!foldl_accepts<int (*)(int &, const int &)>);

int main() {
  L xs = L::cons(1, L::cons(2, L::cons(3, L::nil())));
  L ys = CallableOps::map<int, int>([](const int &x) { return x + 1; }, xs);
  int sum = CallableOps::foldl<int, int>([](int &&acc, const int &x) { return acc + x; }, 0, ys);
  assert(sum == 9);
  int c = CallableConstraintCategories::curry<int, int, int>(
      [](P &&p) { return p.first * 10 + p.second; }, 1, 2);
  assert(c == 12);
  return 0;
}
