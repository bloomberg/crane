#ifndef INCLUDED_SEP_EXT_SIGT_DEPENDENT
#define INCLUDED_SEP_EXT_SIGT_DEPENDENT

#include <any>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &_sv = *this;
    const auto &[x0, a1] = _sv;
    return x0;
  }
};
enum class Tag { TAGA, TAGB, TAGC };
using tag_type = std::any;

struct Packer {
  static inline const SigT<Tag, tag_type> pack_a =
      SigT<Tag, std::any>::existt(Tag::TAGA, std::monostate{});
  static SigT<Tag, tag_type> pack_b(unsigned int n);
  static SigT<Tag, tag_type> pack_c(bool b);
  static Tag get_tag(const SigT<Tag, tag_type> &_x0);
};

#endif // INCLUDED_SEP_EXT_SIGT_DEPENDENT
