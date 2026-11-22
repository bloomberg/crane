#include "bake_array_of_nodes.h"

uint64_t BakeArrayOfNodes::root(const BakeArrayOfNodes::tree &t) {
  if (std::holds_alternative<typename BakeArrayOfNodes::tree::Leaf>(t.v())) {
    return UINT64_C(9);
  } else {
    const auto &[_, a1, _] =
        std::get<typename BakeArrayOfNodes::tree::Node>(t.v());
    return a1;
  }
}

// Baked by crane::bake: the value of crane_baked_nodes_fb0a63562a10.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_nodes_fb0a63562a10_words[] = {
    1, 4,        // BakeArrayOfNodes::tree: #0 to #3
    0,           // #0 Leaf
    1, 0, 3, 0,  // #1 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #2 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #3 Node{a0 = #0, a1 = 3, a2 = #0}
    0,           // end of the nodes
    2, 3, 2, 1,  // the value: [default #3, #2, #1]
};
constinit const crane::bake::image crane_baked_nodes_fb0a63562a10{
    crane_baked_nodes_fb0a63562a10_words, 20, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_lists_04054c02b2fe.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_lists_04054c02b2fe_words[] = {
    1, 5,        // List<unsigned long long>: #0 to #4
    0,           // #0 Nil
    1, 2, 0,     // #1 Cons{a = 2, l = #0}
    1, 1, 1,     // #2 Cons{a = 1, l = #1}
    1, 1, 1,     // #3 Cons{a = 1, l = #1}
    1, 1, 1,     // #4 Cons{a = 1, l = #1}
    0,           // end of the nodes
    2, 4, 3, 2,  // the value: [default #4, #3, #2]
};
constinit const crane::bake::image crane_baked_lists_04054c02b2fe{
    crane_baked_lists_04054c02b2fe_words, 20, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_opts_13fb0669e0ad.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_opts_13fb0669e0ad_words[] = {
    1, 4,                 // BakeArrayOfNodes::tree: #0 to #3
    0,                    // #0 Leaf
    1, 0, 4, 0,           // #1 Node{a0 = #0, a1 = 4, a2 = #0}
    1, 0, 4, 0,           // #2 Node{a0 = #0, a1 = 4, a2 = #0}
    1, 0, 4, 0,           // #3 Node{a0 = #0, a1 = 4, a2 = #0}
    0,                    // end of the nodes
    2, 1, 3, 1, 2, 1, 1,  // the value: [default #3, #2, #1]
};
constinit const crane::bake::image crane_baked_opts_13fb0669e0ad{
    crane_baked_opts_13fb0669e0ad_words, 23, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_empties_807f3bd534db.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_empties_807f3bd534db_words[] = {
    1, 1,           // List<unsigned long long>: #0
    0,              // #0 Nil
    0,              // end of the nodes
    3, 0, 0, 0, 0,  // the value: [default #0, #0, #0, #0]
};
constinit const crane::bake::image crane_baked_empties_807f3bd534db{
    crane_baked_empties_807f3bd534db_words, 9, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_nested_42e6117f3d38.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_nested_42e6117f3d38_words[] = {
    1, 6,        // BakeArrayOfNodes::tree: #0 to #5
    0,           // #0 Leaf
    1, 0, 3, 0,  // #1 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #2 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #3 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #4 Node{a0 = #0, a1 = 3, a2 = #0}
    1, 0, 3, 0,  // #5 Node{a0 = #0, a1 = 3, a2 = #0}
    0,           // end of the nodes
    // the value: [default [default #5, #2, #1], [default #4, #2, #1],
    // [default #3, #2, #1]]
    2, 2, 5, 2, 1, 2, 4, 2, 1, 2, 3, 2, 1,
};
constinit const crane::bake::image crane_baked_nested_42e6117f3d38{
    crane_baked_nested_42e6117f3d38_words, 37, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_leaves_749bec28618a.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_leaves_749bec28618a_words[] = {
    1, 1,        // BakeArrayOfNodes::tree: #0
    0,           // #0 Leaf
    0,           // end of the nodes
    2, 0, 0, 0,  // the value: [default #0, #0, #0]
};
constinit const crane::bake::image crane_baked_leaves_749bec28618a{
    crane_baked_leaves_749bec28618a_words, 8, nullptr, 0, nullptr, 0};
