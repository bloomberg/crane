#include "ParserAnyCast.h"

#include "Ascii.h"
#include "Datatypes.h"
#include "List.h"
#include "ListDef.h"
#include "Specif.h"
#include "String_.h"

namespace ParserAnyCast {

ParserAnyCast::Tag ParserAnyCast::get_tag(ParserAnyCast::entry _x0) {
  return _x0.projT1();
}

Datatypes::List<ParserAnyCast::Tag> ParserAnyCast::process_entries(
    const Datatypes::List<Specif::SigT<ParserAnyCast::Tag, std::any>> &es) {
  return es.template map<ParserAnyCast::Tag>(get_tag);
}

uint64_t ParserAnyCast::get_a_value(
    const Specif::SigT<ParserAnyCast::Tag, std::any> &e) {
  const auto &[x0, a1] = e;
  switch (x0) {
  case Tag::A: {
    return a1;
  }
  case Tag::B: {
    return UINT64_C(0);
  }
  default:
    std::unreachable();
  }
}

uint64_t ParserAnyCast::sum_a_entries(
    const Datatypes::List<Specif::SigT<ParserAnyCast::Tag, std::any>> &es) {
  return es.template fold_left<uint64_t>(
      [](uint64_t acc, const auto &e) { return (acc + get_a_value(e)); },
      UINT64_C(0));
}

} // namespace ParserAnyCast
