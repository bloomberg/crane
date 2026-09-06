#include "sep_ext_sigt_dependent.h"

SigT<Tag, tag_type> Packer::pack_b(uint64_t n) {
  return SigT<Tag, std::any>::existt(Tag::TAGB, n);
}

SigT<Tag, tag_type> Packer::pack_c(bool b) {
  return SigT<Tag, std::any>::existt(Tag::TAGC, b);
}

Tag Packer::get_tag(const SigT<Tag, tag_type> &x0_) { return x0_.projT1(); }
