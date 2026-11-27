// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::hash<T>: a hash for a mapped container keyed by a Rocq value.
// std::hash where the standard library has one; a pair (a Rocq product)
// combines its components' hashes, so a hash map can be keyed by one.

#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <utility>

namespace crane {

template <typename T> struct hash : std::hash<T> {};

// The first component's hash is mixed (the splitmix64 finaliser, a
// bijection) and the second's is xored in unmixed.  std::hash of an integer
// is the identity, so for a dense second component the keys sharing a first
// component stay dense in the low bits, which a hash trie reads first, and
// two keys collide only if the mixed first hashes differ in exactly the bits
// the second components do.
inline std::size_t mix_hash(std::uint64_t z) noexcept {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return static_cast<std::size_t>(z ^ (z >> 31));
}

template <typename A, typename B> struct hash<std::pair<A, B>> {
  std::size_t operator()(const std::pair<A, B> &p) const noexcept {
    return mix_hash(hash<A>{}(p.first)) ^ hash<B>{}(p.second);
  }
};

} // namespace crane
