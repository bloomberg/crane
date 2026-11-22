#include "bake_bde.h"

#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

namespace BloombergLP {}

// Baked by crane::bake: the value of crane_baked_table_a2f71269616f.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_table_a2f71269616f_words[] = {
    1, 4,     // List<unsigned int>: #0 to #3
    0,        // #0 Nil
    1, 3, 0,  // #1 Cons{d_a = 3, d_l = #0}
    1, 2, 1,  // #2 Cons{d_a = 2, d_l = #1}
    1, 1, 2,  // #3 Cons{d_a = 1, d_l = #2}
    0,        // end of the nodes
    3,        // the value: #3
};
constinit const crane::bake::image crane_baked_table_a2f71269616f{
    crane_baked_table_a2f71269616f_words, 14, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_pair_8a1742e7a213.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_pair_8a1742e7a213_words[] = {
    0,     // no nodes
    1, 5,  // the value: {1, 5}
};
constinit const crane::bake::image crane_baked_pair_8a1742e7a213{
    crane_baked_pair_8a1742e7a213_words, 3, nullptr, 0, nullptr, 0};
