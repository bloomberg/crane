// A generated value type's re-defaulted moves are noexcept exactly when its
// payload's moves are: an unconditional `noexcept` would turn a throwing
// element move into std::terminate.  The same holds for crane::variant, the
// storage `Set Crane FastVariant` uses, whose assignments leave it valueless
// -- holding no alternative -- when building the new one throws.
#include "defaulted_move_noexcept.h"
#include "crane_variant.h"

#include <cassert>
#include <stdexcept>
#include <type_traits>

struct Throws {
  Throws() = default;
  Throws(const Throws &) = default;
  Throws(Throws &&) noexcept(false) {}
  Throws &operator=(const Throws &) = default;
  Throws &operator=(Throws &&) noexcept(false) { return *this; }
};

template <class A> using Seq = DefaultedMoveNoexcept::seq<A>;

static_assert(std::is_nothrow_move_constructible_v<Seq<int>>);
static_assert(std::is_nothrow_move_assignable_v<Seq<int>>);
static_assert(!std::is_nothrow_move_constructible_v<Seq<Throws>>);
static_assert(!std::is_nothrow_move_assignable_v<Seq<Throws>>);

static_assert(std::is_nothrow_move_constructible_v<crane::variant<int, long>>);
static_assert(std::is_nothrow_move_assignable_v<crane::variant<int, long>>);
static_assert(!std::is_nothrow_move_constructible_v<crane::variant<int, Throws>>);
static_assert(!std::is_nothrow_move_assignable_v<crane::variant<int, Throws>>);

struct Boom {
  Boom() = default;
  Boom(const Boom &) { throw std::runtime_error("copy"); }
};

int main() {
  using V = crane::variant<int, Boom>;
  V v(1);
  V w(std::in_place_index<1>);
  bool threw = false;
  try {
    v = w;
  } catch (const std::runtime_error &) {
    threw = true;
  }
  assert(threw);
  assert(!v.holds<int>() && !v.holds<Boom>());
  v = V(2);
  assert(v.holds<int>() && crane::get<int>(v) == 2);
  return 0;
}
