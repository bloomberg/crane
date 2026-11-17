#pragma once

#include <cstdint>

#include "Datatypes.h"
#include "List.h"

namespace SepExtCrossModule {
uint64_t sum_list(const Datatypes::List<uint64_t> &l);
Datatypes::List<uint64_t> make_pair_list(uint64_t n, uint64_t m);
} // namespace SepExtCrossModule
