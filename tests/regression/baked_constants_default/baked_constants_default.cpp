#include "baked_constants_default.h"

/// build n has 2^n - 1 nodes, but only n distinct ones: each node's
/// two children are one value.
BakedConstantsDefault::tree BakedConstantsDefault::build(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t m = n - 1;
    BakedConstantsDefault::tree t = build(m);
    return tree::node(t, n, t);
  }
}

uint64_t BakedConstantsDefault::size(const BakedConstantsDefault::tree &t) {
  if (std::holds_alternative<typename BakedConstantsDefault::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, _, r0] =
        std::get<typename BakedConstantsDefault::tree::Node>(t.v());
    return ((UINT64_C(1) + size(*l0)) + size(*r0));
  }
}

uint64_t BakedConstantsDefault::sum_tree(const BakedConstantsDefault::tree &t) {
  if (std::holds_alternative<typename BakedConstantsDefault::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, x0, r0] =
        std::get<typename BakedConstantsDefault::tree::Node>(t.v());
    return ((sum_tree(*l0) + x0) + sum_tree(*r0));
  }
}

/// Baked: a table of rows, two of them the same row.
crane::shared_array<uint64_t> BakedConstantsDefault::row(uint64_t k) {
  return vec_of_list<uint64_t>(
      ListDef::seq(UINT64_C(0), UINT64_C(10)).template map<uint64_t>(
          [=](uint64_t i) { return (i * k); }));
}

uint64_t BakedConstantsDefault::big_size() { return size(big); }

uint64_t BakedConstantsDefault::big_sum() { return sum_tree(big); }

uint64_t BakedConstantsDefault::cell(uint64_t i, uint64_t j) {
  auto _once1 = table.first;
  auto _once2 = (static_cast<std::size_t>(i) < (_once1).size()
                     ? (_once1)[static_cast<std::size_t>(i)]
                     : crane::shared_array<uint64_t>{});
  return (static_cast<std::size_t>(j) < (_once2).size() ? (_once2)[static_cast<
                                                               std::size_t>(j)]
                                                        : UINT64_C(0));
}

bool BakedConstantsDefault::accept(uint64_t i) {
  auto _once1 = table.second;
  return (static_cast<std::size_t>(i) < (_once1).size() ? (_once1)[static_cast<
                                                               std::size_t>(i)]
                                                        : false);
}

std::string BakedConstantsDefault::names() {
  return entries.template fold_right<std::string>(
      [](const BakedConstantsDefault::entry &e,
         std::string acc) { return String0::append(e.name, std::move(acc)); },
      std::string());
}

uint64_t BakedConstantsDefault::weights() {
  return entries.template fold_right<uint64_t>(
      [](const BakedConstantsDefault::entry &e, uint64_t acc) -> uint64_t {
        if (e.weight.has_value()) {
          const uint64_t &w = *e.weight;
          return (w + acc);
        } else {
          return acc;
        }
      },
      UINT64_C(0));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}

std::string String0::append(const std::string &s1, std::string s2) {
  if (s1.empty()) {
    return s2;
  } else {
    char c = s1[0];
    std::string s1_ = s1.substr(1);
    return std::string(1, c) + String0::append(s1_, std::move(s2));
  }
}

// Baked by crane::bake: the value of crane_baked_table_6bda686fed62.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_6bda686fed62_b0{
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_6bda686fed62_b1{
    0, 3, 6, 9, 12, 15, 18, 21, 24, 27};
[[clang::no_destroy]] constinit crane::shared_array<crane::shared_array<unsigned long long>>::fixed<4> crane_baked_table_6bda686fed62_b2{
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b0),
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b1),
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b1),
    crane::shared_array<unsigned long long>{}};
[[clang::no_destroy]] constinit crane::shared_array<bool>::fixed<3> crane_baked_table_6bda686fed62_b3{
    true, false, true};
constinit const void *const crane_baked_table_6bda686fed62_blocks[] = {
    &crane_baked_table_6bda686fed62_b2, &crane_baked_table_6bda686fed62_b3};
constinit const std::uint64_t crane_baked_table_6bda686fed62_words[] = {
    0,                     // no nodes
    2, 0, 2488, 2, 1, 17,  // the value: {b2, b3}
};
constinit const crane::bake::image crane_baked_table_6bda686fed62{
    crane_baked_table_6bda686fed62_words, 7,
    crane_baked_table_6bda686fed62_blocks, 2, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_big_6a150784210f.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_big_6a150784210f_words[] = {
    1, 32,          // BakedConstantsDefault::tree: #0 to #31
    0,              // #0 Leaf
    1, 0, 1, 0,     // #1 Node{l = #0, x = 1, r = #0}
    1, 0, 1, 0,     // #2 Node{l = #0, x = 1, r = #0}
    1, 1, 2, 2,     // #3 Node{l = #1, x = 2, r = #2}
    1, 1, 2, 2,     // #4 Node{l = #1, x = 2, r = #2}
    1, 3, 3, 4,     // #5 Node{l = #3, x = 3, r = #4}
    1, 3, 3, 4,     // #6 Node{l = #3, x = 3, r = #4}
    1, 5, 4, 6,     // #7 Node{l = #5, x = 4, r = #6}
    1, 5, 4, 6,     // #8 Node{l = #5, x = 4, r = #6}
    1, 7, 5, 8,     // #9 Node{l = #7, x = 5, r = #8}
    1, 7, 5, 8,     // #10 Node{l = #7, x = 5, r = #8}
    1, 9, 6, 10,    // #11 Node{l = #9, x = 6, r = #10}
    1, 9, 6, 10,    // #12 Node{l = #9, x = 6, r = #10}
    1, 11, 7, 12,   // #13 Node{l = #11, x = 7, r = #12}
    1, 11, 7, 12,   // #14 Node{l = #11, x = 7, r = #12}
    1, 13, 8, 14,   // #15 Node{l = #13, x = 8, r = #14}
    1, 13, 8, 14,   // #16 Node{l = #13, x = 8, r = #14}
    1, 15, 9, 16,   // #17 Node{l = #15, x = 9, r = #16}
    1, 15, 9, 16,   // #18 Node{l = #15, x = 9, r = #16}
    1, 17, 10, 18,  // #19 Node{l = #17, x = 10, r = #18}
    1, 17, 10, 18,  // #20 Node{l = #17, x = 10, r = #18}
    1, 19, 11, 20,  // #21 Node{l = #19, x = 11, r = #20}
    1, 19, 11, 20,  // #22 Node{l = #19, x = 11, r = #20}
    1, 21, 12, 22,  // #23 Node{l = #21, x = 12, r = #22}
    1, 21, 12, 22,  // #24 Node{l = #21, x = 12, r = #22}
    1, 23, 13, 24,  // #25 Node{l = #23, x = 13, r = #24}
    1, 23, 13, 24,  // #26 Node{l = #23, x = 13, r = #24}
    1, 25, 14, 26,  // #27 Node{l = #25, x = 14, r = #26}
    1, 25, 14, 26,  // #28 Node{l = #25, x = 14, r = #26}
    1, 27, 15, 28,  // #29 Node{l = #27, x = 15, r = #28}
    1, 27, 15, 28,  // #30 Node{l = #27, x = 15, r = #28}
    1, 29, 16, 30,  // #31 Node{l = #29, x = 16, r = #30}
    0,              // end of the nodes
    31,             // the value: #31
};
constinit const crane::bake::image crane_baked_big_6a150784210f{
    crane_baked_big_6a150784210f_words, 129, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_entries_9913efaaf321.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_entries_9913efaaf321_text0[] = "first";
constinit const std::string_view crane_baked_entries_9913efaaf321_text[] = {
    std::string_view(crane_baked_entries_9913efaaf321_text0, 5)};
constinit const std::uint64_t crane_baked_entries_9913efaaf321_words[] = {
    2, 4,              // BakedConstantsDefault::tree: #0 to #3
    0,                 // #0 Leaf
    1, 0, 1, 0,        // #1 Node{l = #0, x = 1, r = #0}
    1, 0, 1, 0,        // #2 Node{l = #0, x = 1, r = #0}
    1, 1, 2, 2,        // #3 Node{l = #1, x = 2, r = #2}
    1, 3,              // List<BakedConstantsDefault::entry>: #4 to #6
    0,                 // #4 Nil
    // #5 Cons{a = entry{name = "", weight = nullopt, label = #0}, l = #4}
    1, 0, 0, 0, 4,
    // #6 Cons{a = entry{name = "first", weight = 7, label = #3}, l = #5}
    1, 5, 1, 7, 3, 5,
    0,                 // end of the nodes
    6,                 // the value: #6
};
constinit const crane::bake::image crane_baked_entries_9913efaaf321{
    crane_baked_entries_9913efaaf321_words, 31, nullptr, 0,
    crane_baked_entries_9913efaaf321_text, 1};
