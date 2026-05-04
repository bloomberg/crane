#ifndef INCLUDED_SEPEXTCROSSMODULE
#define INCLUDED_SEPEXTCROSSMODULE

#include <memory>
#include <optional>
#include <type_traits>

#include "Datatypes.h"
#include "List.h"

unsigned int sum_list(const List<unsigned int> &l);
List<unsigned int> make_pair_list(const unsigned int n, const unsigned int m);

#endif // INCLUDED_SEPEXTCROSSMODULE
