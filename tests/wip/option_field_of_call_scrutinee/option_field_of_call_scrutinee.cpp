#include "option_field_of_call_scrutinee.h"

OptionFieldOfCallScrutinee::box OptionFieldOfCallScrutinee::mk(uint64_t n) {
  return box{std::make_optional<List<uint64_t>>(ListDef::seq(UINT64_C(0), n))};
}

uint64_t OptionFieldOfCallScrutinee::count(uint64_t n) {
  if (mk(n).sub.has_value()) {
    const List<uint64_t> &l = *mk(n).sub;
    return l.length();
  } else {
    return UINT64_C(0);
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
