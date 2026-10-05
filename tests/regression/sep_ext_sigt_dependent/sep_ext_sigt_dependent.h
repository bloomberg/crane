#ifndef INCLUDED_SEP_EXT_SIGT_DEPENDENT
#define INCLUDED_SEP_EXT_SIGT_DEPENDENT

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;
enum class Tag;
using tag_type = crane::obj;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }
};
enum class Tag { TAGA, TAGB, TAGC };

struct Packer {
  static inline const SigT<Tag, tag_type> pack_a =
      SigT<Tag, tag_type>::existt(Tag::TAGA, std::monostate{});
  static SigT<Tag, tag_type> pack_b(uint64_t n);
  static SigT<Tag, tag_type> pack_c(bool b);
  static Tag get_tag(const SigT<Tag, tag_type> &x0_);
};

#endif // INCLUDED_SEP_EXT_SIGT_DEPENDENT
