#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <mini_stm.h>
#include <skiplist_bde.h>
#include <skipnode.h>

namespace BloombergLP {

}
bool Nat::eqb(const unsigned int n, const unsigned int m)
{
    if (n <= 0) {
        if (m <= 0) {
            return true;
        }
        else {
            unsigned int _x = m - 1;
            return false;
        }
    }
    else {
        unsigned int n_ = n - 1;
        if (m <= 0) {
            return false;
        }
        else {
            unsigned int m_ = m - 1;
            return eqb(n_, m_);
        }
    }
}

bool Nat::leb(const unsigned int n, const unsigned int m)
{
    if (n <= 0) {
        return true;
    }
    else {
        unsigned int n_ = n - 1;
        if (m <= 0) {
            return false;
        }
        else {
            unsigned int m_ = m - 1;
            return leb(n_, m_);
        }
    }
}

bool Nat::ltb(const unsigned int n, const unsigned int m)
{
    return leb((bsl::move(n) + 1), m);
}
