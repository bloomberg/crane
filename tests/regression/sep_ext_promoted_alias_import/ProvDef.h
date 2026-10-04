#ifndef INCLUDED_PROVDEF
#define INCLUDED_PROVDEF

#include "obj.h"
#include <any>
#include <concepts>

namespace ProvDef {

using prov = crane::obj;
template <typename
I>concept Provenance = requires {
    typename I::prov;
  } && (requires {
    { I::nil_prov() } -> std::convertible_to<typename I::prov>;
  } || requires {
    { I::nil_prov } -> std::convertible_to<typename I::prov>;
  });

} // namespace ProvDef

#endif // INCLUDED_PROVDEF
