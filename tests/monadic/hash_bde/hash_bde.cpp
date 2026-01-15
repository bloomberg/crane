#include <bdlf_overloaded.h>
#include <bsl_algorithm.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <fstream>
#include <hash_bde.h>
#include <mini_stm.h>

namespace BloombergLP {

}
int CHT::max(const int a, const int b)
{
    if (a < b) {
        return b;
    }
    else {
        return a;
    }
}
