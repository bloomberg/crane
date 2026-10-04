#ifndef INCLUDED_PARAMSDEF
#define INCLUDED_PARAMSDEF

#include "obj.h"
#include <any>
#include <concepts>

namespace ParamsDef {

enum class Provenance;
using prov = crane::obj;
template <typename I>
concept Params = requires {
  { I::PROV() } -> std::convertible_to<Provenance>;
};
enum class Provenance { BUILD_PROVENANCE };

} // namespace ParamsDef

#endif // INCLUDED_PARAMSDEF
