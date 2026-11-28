#pragma once

#include <cstdint>

struct DemotedDictionaryOperation {
  /// A class of the shape of ST.Code: a number for a type.
  template <typename A> struct Tag {
    uint64_t tag;

    // ACCESSORS
    template <typename CraneU> operator Tag<CraneU>() const { return {tag}; }
  };

  static Tag<uint64_t> tag_of(uint64_t n);

  /// Generic over the dictionary, which it holds as a value.
  template <typename T1>
  static uint64_t diff(const Tag<T1> &, uint64_t x1_, uint64_t x2_) {
    return x1_ - x2_;
  }

  /// The dictionary read as data, next to the operation.
  template <typename T1>
  static uint64_t diff_plus_tag(const Tag<T1> &h, uint64_t x, uint64_t y) {
    return (x - y) + h.tag;
  }

  static inline const uint64_t seven =
      diff<uint64_t>(tag_of(UINT64_C(100)), UINT64_C(10), UINT64_C(3));
  static inline const uint64_t seventeen =
      diff_plus_tag<uint64_t>(tag_of(UINT64_C(10)), UINT64_C(10), UINT64_C(3));
};
