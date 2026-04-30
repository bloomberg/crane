#include <topological_sort_bde.h>

#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_optional.h>
#include <bsl_utility.h>
#include <bsl_string.h>
#include <bsl_memory.h>


namespace BloombergLP {

}
List<unsigned int> ListDef::seq(unsigned int start,
const unsigned int& len){if (len <= 0) { return List<unsigned int>::nil(); } else { unsigned int len0 = len - 1; return List<unsigned int>::cons(start,
ListDef::seq((start + 1),
len0)); }}
