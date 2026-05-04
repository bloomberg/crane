#ifndef INCLUDED_SEPEXTCROSSMODULE
#define INCLUDED_SEPEXTCROSSMODULE

#include <memory>
#include <optional>
#include <type_traits>

#include "Datatypes.h"
#include "List.h"

namespace SepExtCrossModule {

unsigned int sum_list(const Datatypes::List<unsigned int> &l);
Datatypes::List<unsigned int> make_pair_list(const unsigned int n,
                                             const unsigned int m);

} // namespace SepExtCrossModule

#endif // INCLUDED_SEPEXTCROSSMODULE
