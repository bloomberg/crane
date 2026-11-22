#include "bake_prim_string.h"

// Baked by crane::bake: the value of crane_baked_words_56303450632f.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_words_56303450632f_text0[] = "cde" "ab";
constinit const std::string_view crane_baked_words_56303450632f_text[] = {
    std::string_view(crane_baked_words_56303450632f_text0, 5)};
constinit const std::uint64_t crane_baked_words_56303450632f_words[] = {
    1, 3,     // List<std::string>: #0 to #2
    0,        // #0 Nil
    1, 3, 0,  // #1 Cons{a = "cde", l = #0}
    1, 2, 1,  // #2 Cons{a = "ab", l = #1}
    0,        // end of the nodes
    2,        // the value: #2
};
constinit const crane::bake::image crane_baked_words_56303450632f{
    crane_baked_words_56303450632f_words, 11, nullptr, 0,
    crane_baked_words_56303450632f_text, 1};

// Baked by crane::bake: the value of crane_baked_greeting_5eb3a447a71f.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_greeting_5eb3a447a71f_text0[] = "abcd";
constinit const std::string_view crane_baked_greeting_5eb3a447a71f_text[] = {
    std::string_view(crane_baked_greeting_5eb3a447a71f_text0, 4)};
constinit const std::uint64_t crane_baked_greeting_5eb3a447a71f_words[] = {
    0,  // no nodes
    4,  // the value: "abcd"
};
constinit const crane::bake::image crane_baked_greeting_5eb3a447a71f{
    crane_baked_greeting_5eb3a447a71f_words, 2, nullptr, 0,
    crane_baked_greeting_5eb3a447a71f_text, 1};
