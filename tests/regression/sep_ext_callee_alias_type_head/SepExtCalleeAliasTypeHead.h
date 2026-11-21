#pragma once

#include <cstdint>
#include <utility>

#include "Datatypes.h"
#include "Inst.h"

namespace SepExtCalleeAliasTypeHead {
uint64_t lex_rules(const Datatypes::List<uint64_t> &x0_);
const uint64_t result = lex_rules(Datatypes::template List<uint64_t>::cons(
    UINT64_C(4), Datatypes::template List<uint64_t>::nil()));
} // namespace SepExtCalleeAliasTypeHead
