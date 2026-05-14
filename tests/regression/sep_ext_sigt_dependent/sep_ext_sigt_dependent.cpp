#include "sep_ext_sigt_dependent.h"

SigT<Tag, tag_type> Packer::pack_b(const unsigned int n) {
  return SigT<Tag, std::any>::existt(Tag::e_TAGB, n);
}

SigT<Tag, tag_type> Packer::pack_c(const bool b) {
  return SigT<Tag, std::any>::existt(Tag::e_TAGC, b);
}

Tag Packer::get_tag(const SigT<Tag, tag_type> &_x0) { return _x0.projT1(); }
