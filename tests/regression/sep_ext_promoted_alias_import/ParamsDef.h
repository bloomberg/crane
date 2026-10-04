#ifndef INCLUDED_PARAMSDEF
#define INCLUDED_PARAMSDEF

#include "obj.h"
#include <any>
#include <concepts>
#include <utility>

namespace ParamsDef {

using ptr = crane::obj;
template <typename I, typename prov>
concept Pointer = requires {
  typename I::ptr;
  { I::mk_ptr(std::declval<prov>()) } -> std::convertible_to<typename I::ptr>;
};
template <typename I, typename prov>
concept Params = requires {
  typename I::PROV;
  typename I::PTR;
};

} // namespace ParamsDef

#endif // INCLUDED_PARAMSDEF
