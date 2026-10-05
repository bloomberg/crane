#ifndef INCLUDED_SEPEXTPAIRNESTEDANY
#define INCLUDED_SEPEXTPAIRNESTEDANY

#include "obj.h"
#include <memory>
#include <optional>
#include <utility>

#include "Datatypes.h"
#include "Specif.h"

namespace SepExtPairNestedAny {

using sem_ty = crane::obj;
using token = Specif::SigT<Datatypes::Nat, sem_ty>;
const std::pair<std::optional<Datatypes::List<token>>, bool> produce =
    std::make_pair(
        std::optional<
            Datatypes::List<Specif::SigT<Datatypes::Nat, crane::obj>>>(),
        true);

inline constexpr bool use_it = true;

} // namespace SepExtPairNestedAny

#endif // INCLUDED_SEPEXTPAIRNESTEDANY
