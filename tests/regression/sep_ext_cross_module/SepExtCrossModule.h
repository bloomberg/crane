#ifndef INCLUDED_SEPEXTCROSSMODULE
#define INCLUDED_SEPEXTCROSSMODULE

#include "Datatypes.h"
#include "List.h"

namespace SepExtCrossModule {

unsigned int sum_list(const Datatypes::List<unsigned int> &l);
Datatypes::List<unsigned int> make_pair_list(unsigned int n, unsigned int m);

} // namespace SepExtCrossModule

#endif // INCLUDED_SEPEXTCROSSMODULE
