#include <bdlf_overloaded.h>
#include <benchmark.h>
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

using namespace BloombergLP;

namespace unit {
bsl::shared_ptr<unit> tt::make()
{
    return bsl::make_shared<unit>(tt{});
}
};

namespace list {

};

std::string benchmark(const bsl::shared_ptr<unit::unit> _x)
{
    return ToString::list_to_string<
        bsl::shared_ptr<list::list<unsigned int> > >(
                    [&](const bsl::shared_ptr<list::list<unsigned int> > _x0) {
                        return ToString::list_to_string<unsigned int>(
                            [&](const unsigned int _x0) {
                                return std::to_string(_x0);
                            },
                            _x0);
                    },
                    TopSort::topological_sort_graph<unsigned int>(
                        [&](const unsigned int _x0, const unsigned int _x1) {
                            return (_x0 == _x1);
                        },
                        bigDAG));
}
