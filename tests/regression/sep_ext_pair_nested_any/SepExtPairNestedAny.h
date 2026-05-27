#ifndef INCLUDED_SEPEXTPAIRNESTEDANY
#define INCLUDED_SEPEXTPAIRNESTEDANY

#include <any>
#include <memory>
#include <optional>
#include <utility>

#include "Datatypes.h"
#include "Specif.h"

namespace SepExtPairNestedAny {

using sem_ty = std::any;
using token = Specif::SigT<Datatypes::Nat, sem_ty>;
const std::pair<std::optional<Datatypes::List<token>>, bool> produce =
    std::make_pair(
        std::optional<
            Datatypes::List<Specif::SigT<Datatypes::Nat, std::any>>>(),
        true);
const bool use_it = []() -> bool {
  auto _x = std::move(produce.first);
  bool b = std::move(produce.second);
  return b;
}();

} // namespace SepExtPairNestedAny

#endif // INCLUDED_SEPEXTPAIRNESTEDANY
