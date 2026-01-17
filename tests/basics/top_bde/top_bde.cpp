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
#include <top_bde.h>

namespace BloombergLP {

}
bsl::shared_ptr<List::list<unsigned int> > seq(const unsigned int start,
                                               const unsigned int len)
{
    if (len <= 0) {
        return List::list<unsigned int>::ctor::nil_();
    }
    else {
        unsigned int len0 = len - 1;
        return List::list<unsigned int>::ctor::cons_(start,
                                                     seq((start + 1), len0));
    }
}
