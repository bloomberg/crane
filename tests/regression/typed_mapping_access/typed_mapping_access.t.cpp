// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Parameter access planning: each parameter of a typed-mapped type takes the
// form its uses require, joined across direct calls.
#include <typed_mapping_access.h>

#include <cstdint>
#include <iostream>
#include <type_traits>
#include <vector>

using T = TypedMappingAccess;
using access_support::buf;
using access_support::handle;

// Reads only: canonical read (MutableHandle HandleByConstReference).
static_assert(std::is_same_v<decltype(&T::peek), uint64_t (*)(const handle &)>);
static_assert(
    std::is_same_v<decltype(&T::buf_size), uint64_t (*)(const buf &)>);
// Writes through the handle at every level: the write-through form of a
// handle is its read form.
static_assert(std::is_same_v<decltype(&T::poke),
                             handle (*)(const handle &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::poke_middle),
                             handle (*)(const handle &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::poke_outer),
                             uint64_t (*)(const handle &, uint64_t)>);
// Replace: T&, at every level.
static_assert(
    std::is_same_v<decltype(&T::reseat), uint64_t (*)(handle &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::reseat_outer),
                             uint64_t (*)(handle &, uint64_t)>);
// Take: by value, whatever else the body does.
static_assert(std::is_same_v<decltype(&T::keep), handle (*)(handle)>);
static_assert(
    std::is_same_v<decltype(&T::keep_and_reseat), uint64_t (*)(handle)>);
// Writes a mutable value in place: T&, at every level of the chain.
static_assert(
    std::is_same_v<decltype(&T::push), buf (*)(buf &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::push_middle), buf (*)(buf &)>);
static_assert(std::is_same_v<decltype(&T::push_outer), uint64_t (*)(buf &)>);
// A recursive group: pong only passes its handle to ping, which reseats it.
static_assert(
    std::is_same_v<decltype(&T::pong), uint64_t (*)(handle &, uint64_t)>);
static_assert(
    std::is_same_v<decltype(&T::ping), uint64_t (*)(handle &, uint64_t)>);
// Named as a value: the canonical by-value ABI, which a callable taking the
// handle by const reference can call.
static_assert(
    std::is_same_v<decltype(&T::reseat_value), uint64_t (*)(handle)>);
static_assert(
    std::is_same_v<decltype(&T::through_value), uint64_t (*)(const handle &)>);
// Self recursion.
static_assert(std::is_same_v<decltype(&T::reseat_loop),
                             uint64_t (*)(handle &, uint64_t)>);
static_assert(
    std::is_same_v<decltype(&T::push_loop), uint64_t (*)(buf &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::reseat_sum),
                             uint64_t (*)(handle &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::reseat_each),
                             uint64_t (*)(handle &, const List<uint64_t> &)>);
static_assert(std::is_same_v<decltype(&T::push_each),
                             uint64_t (*)(buf &, const List<uint64_t> &)>);
static_assert(std::is_same_v<decltype(&T::push_all),
                             List<uint64_t> (*)(buf &, const List<uint64_t> &)>);
static_assert(std::is_same_v<decltype(&T::reseat_down),
                             uint64_t (*)(handle &, const List<uint64_t> &)>);

// Under a closure a parameter is a copy the closure holds: a closure's
// replacement does not reach the caller, so the parameter is only read.
static_assert(std::is_same_v<decltype(&T::reseat_captured),
                             List<uint64_t> (*)(const handle &,
                                                const List<uint64_t> &)>);

static int failures = 0;

static void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAIL: " << what << "\n";
    ++failures;
  }
}

static List<uint64_t> list(std::vector<uint64_t> xs) {
  List<uint64_t> l = List<uint64_t>::nil();
  for (auto it = xs.rbegin(); it != xs.rend(); ++it)
    l = List<uint64_t>::cons(*it, l);
  return l;
}

int main() {
  handle h = access_support::make(5);
  check(T::peek(h) == 5, "peek");

  // Writes go through the handle the caller holds.
  check(T::poke_outer(h, 1) == 3, "poke_outer");
  check(access_support::get(h) == 3, "poke_outer writes through the handle");

  // Replace reseats the caller's handle.
  handle before = h;
  check(T::reseat_outer(h, 8) == 9, "reseat_outer");
  check(access_support::get(h) == 8 && h != before,
        "reseat_outer reseats the caller's handle");
  check(access_support::get(before) == 3, "the old cell is untouched");

  // Take: the callee holds its own copy, which it reseats.
  handle k = T::keep(h);
  check(k == h, "keep returns the handle it is given");
  check(T::keep_and_reseat(h) == 8 + 7, "keep_and_reseat");
  check(access_support::get(h) == 8, "keep_and_reseat reseats its own copy");

  // A mutable value written in place, through every level.
  buf b = access_support::buf_make(2);
  check(T::buf_size(b) == 2, "buf_size");
  check(T::push_outer(b) == 3, "push_outer");
  check(b.items.size() == 3, "push_outer writes the caller's buffer");

  // The recursive group.
  handle g = access_support::make(4);
  check(T::pong(g, 0) == 4, "pong(0)");
  check(T::pong(g, 1) == 9, "pong(1)");
  check(access_support::get(g) == 9, "pong(1) reseats through ping");

  // Through a function value: reseat_value reseats its own copy.
  handle v = access_support::make(6);
  check(T::through_value(v) == 3, "through_value");
  check(access_support::get(v) == 6, "through_value leaves the handle");

  // A value that is not a variable is materialised for the call.
  check(T::reseat_fresh(1) == 4, "reseat_fresh");
  check(T::reseat_fresh_op(1) == 2, "reseat_fresh_op");
  check(T::push_fresh(4) == 5, "push_fresh");

  // Self recursion as a loop: the loop rebinds the caller's handle and
  // writes the caller's buffer through the reference, copying neither.
  handle r = access_support::make(0);
  check(T::reseat_loop(r, 3) == 1, "reseat_loop");
  check(access_support::get(r) == 1, "reseat_loop rebinds the caller's handle");
  buf p = access_support::buf_make(0);
  check(T::push_loop(p, 3) == 3, "push_loop");
  check(p.items.size() == 3, "push_loop writes the caller's buffer");
  handle e = access_support::make(0);
  check(T::reseat_each(e, list({1, 2, 3})) == 3, "reseat_each");
  buf q = access_support::buf_make(1);
  check(T::push_each(q, list({1, 2})) == 3, "push_each");
  // Through a stack of frames: each frame holds the handle it was called
  // with.
  handle d = access_support::make(0);
  check(T::reseat_down(d, list({1, 2, 3})) == 3 + 3, "reseat_down");
  buf a = access_support::buf_make(0);
  T::push_all(a, list({1, 2, 3}));
  check(a.items.size() == 3, "push_all writes the caller's buffer");

  // Closures: each replacement is made on a copy.
  handle c = access_support::make(5);
  T::reseat_captured(c, list({1, 2}));
  check(access_support::get(c) == 5, "reseat_captured leaves the handle");
  List<handle> hs = List<handle>::cons(
      c, List<handle>::cons(access_support::make(7), List<handle>::nil()));
  T::reseat_each_value(hs);
  check(access_support::get(c) == 5, "reseat_each_value leaves the handles");

  if (failures == 0) {
    std::cout << "All typed_mapping_access tests passed!\n";
    return 0;
  }
  return 1;
}
