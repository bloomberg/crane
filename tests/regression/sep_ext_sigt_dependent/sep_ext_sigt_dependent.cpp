#include "sep_ext_sigt_dependent.h"

SigT<Tag, tag_type> Packer::pack_b(unsigned int n) {
  return SigT<Tag, std::any>::existt(Tag::e_TAGB, n);
}

SigT<Tag, tag_type> Packer::pack_c(bool b) {
  return SigT<Tag, std::any>::existt(Tag::e_TAGC, b);
}

Tag Packer::get_tag(const SigT<Tag, tag_type> &_x0) { return _x0.projT1(); }
