#include "bake_boxed_field.h"

// Baked by crane::bake: the value of crane_baked_choice_2999d3bac477.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_choice_2999d3bac477_words[] = {
    2, 3,     // List<unsigned long long>: #0 to #2
    0,        // #0 Nil
    1, 5, 0,  // #1 Cons{a = 5, l = #0}
    1, 4, 1,  // #2 Cons{a = 4, l = #1}
    1, 1,     // Sum<List<unsigned long long>, unsigned long long>: #3
    0, 2,     // #3 Inl{a0 = #2}
    0,        // end of the nodes
    3,        // the value: #3
};
constinit const crane::bake::image crane_baked_choice_2999d3bac477{
    crane_baked_choice_2999d3bac477_words, 15, nullptr, 0, nullptr, 0};
