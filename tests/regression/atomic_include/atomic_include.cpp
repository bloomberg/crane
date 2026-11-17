#include "atomic_include.h"



uint64_t AtomicInclude::size(const AtomicInclude::tree& t){if (crane::holds_alternative<typename AtomicInclude::tree::Leaf>(t.v())) {
return UINT64_C(1);
} else {
const auto& [l0, r0] = crane::get<typename AtomicInclude::tree::Node>(t.v());
return (size(*l0) + size(*r0));
}}

