#include "fn_list_state_alias_fit.h"

FnListStateAliasFit::st<uint64_t> FnListStateAliasFit::h(uint64_t k) {
  return hd_or<crane::fn<FnListStateAliasFit::st<uint64_t>(uint64_t)>>(
      [](uint64_t) { return sret<uint64_t>(UINT64_C(0)); },
      List<crane::fn<FnListStateAliasFit::st<uint64_t>(uint64_t)>>::cons(
          [=](uint64_t j) { return sret<uint64_t>((j + k)); },
          List<crane::fn<FnListStateAliasFit::st<uint64_t>(uint64_t)>>::nil()))(
      UINT64_C(4));
}
