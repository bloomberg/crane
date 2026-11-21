#include "SepExtCalleeAliasTypeHead.h"

#include "Datatypes.h"
#include "Inst.h"

namespace SepExtCalleeAliasTypeHead {
uint64_t lex_rules(const Datatypes::List<uint64_t> &x0_) {
  return Inst::SL::lex_with(
      []() {
        auto _pa0 = Datatypes::template List<uint64_t>::cons(
            UINT64_C(1),
            Datatypes::template List<uint64_t>::cons(
                UINT64_C(2),
                Datatypes::template List<uint64_t>::cons(
                    UINT64_C(3), Datatypes::template List<uint64_t>::nil())));
        return [=](Datatypes::List<uint64_t> _x0) -> std::pair<
            Datatypes::List<Inst::LX::D::Token>,
            Datatypes::List<uint64_t>> { return Inst::LX::lex(_pa0, _x0); };
      }(),
      x0_);
}
} // namespace SepExtCalleeAliasTypeHead
