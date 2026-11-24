#include "sub_self_unused_param.h"

SubSelfUnusedParam::stream SubSelfUnusedParam::sconst(uint64_t n) {
  return stream::lazy_(
      [=]() mutable -> typename SubSelfUnusedParam::stream::SCons {
        return {n, sconst(n)};
      });
}

uint64_t SubSelfUnusedParam::on_box(const SubSelfUnusedParam::box &) {
  return UINT64_C(0);
}

uint64_t SubSelfUnusedParam::on_stream(const SubSelfUnusedParam::stream &) {
  return UINT64_C(0);
}

uint64_t SubSelfUnusedParam::in_branch(bool c,
                                       const SubSelfUnusedParam::box &) {
  if (c) {
    return UINT64_C(0);
  } else {
    return UINT64_C(7);
  }
}
