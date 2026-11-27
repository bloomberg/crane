#include "baked_constants.h"

/// build n has 2^n - 1 nodes, but only n distinct ones: each node's
/// two children are one value.
BakedConstants::tree BakedConstants::build(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t m = n - 1;
    BakedConstants::tree t = build(m);
    return tree::node(t, n, t);
  }
}

uint64_t BakedConstants::size(const BakedConstants::tree &t) {
  if (crane::holds_alternative<typename BakedConstants::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, _, r0] =
        crane::get<typename BakedConstants::tree::Node>(t.v());
    return UINT64_C(1) + size(*l0) + size(*r0);
  }
}

uint64_t BakedConstants::sum_tree(const BakedConstants::tree &t) {
  if (crane::holds_alternative<typename BakedConstants::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, x0, r0] =
        crane::get<typename BakedConstants::tree::Node>(t.v());
    return sum_tree(*l0) + x0 + sum_tree(*r0);
  }
}

/// Baked: a table of rows, two of them the same row.
crane::shared_array<uint64_t> BakedConstants::row(uint64_t k) {
  return vec_of_list<uint64_t>(
      ListDef::seq(UINT64_C(0), UINT64_C(10)).template map<uint64_t>(
          [=](uint64_t i) { return i * k; }));
}

uint64_t BakedConstants::big_size() { return size(big); }

uint64_t BakedConstants::big_sum() { return sum_tree(big); }

uint64_t BakedConstants::cell(uint64_t i, uint64_t j) {
  auto _once1 = table.first;
  auto _once2 = (static_cast<std::size_t>(i) < (_once1).size()
                     ? (_once1)[static_cast<std::size_t>(i)]
                     : crane::shared_array<uint64_t>{});
  return (static_cast<std::size_t>(j) < (_once2).size() ? (_once2)[static_cast<
                                                               std::size_t>(j)]
                                                        : UINT64_C(0));
}

bool BakedConstants::accept(uint64_t i) {
  auto _once1 = table.second;
  return (static_cast<std::size_t>(i) < (_once1).size() ? (_once1)[static_cast<
                                                               std::size_t>(i)]
                                                        : false);
}

std::string BakedConstants::names() {
  return entries.template fold_right<std::string>(
      [](const BakedConstants::entry &e,
         std::string acc) { return String0::append(e.name, std::move(acc)); },
      std::string());
}

uint64_t BakedConstants::weights() {
  return entries.template fold_right<uint64_t>(
      [](const BakedConstants::entry &e, uint64_t acc) -> uint64_t {
        if (e.weight.has_value()) {
          const uint64_t &w = *e.weight;
          return w + acc;
        } else {
          return acc;
        }
      },
      UINT64_C(0));
}

/// What cannot be baked.
uint64_t BakedConstants::twice(uint64_t n) { return n + n; }

BakedConstants::stream BakedConstants::ones() {
  return stream::lazy_([]() -> typename BakedConstants::stream::Cons {
    return {UINT64_C(1), ones()};
  });
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

// Baked by crane::bake: the value of crane_baked_table_c8c1801e8579.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_c8c1801e8579_b0{
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_c8c1801e8579_b1{
    0, 3, 6, 9, 12, 15, 18, 21, 24, 27};
[[clang::no_destroy]] constinit crane::shared_array<crane::shared_array<unsigned long long>>::fixed<4> crane_baked_table_c8c1801e8579_b2{
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_c8c1801e8579_b0),
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_c8c1801e8579_b1),
    crane::shared_array<unsigned long long>::of_static(crane_baked_table_c8c1801e8579_b1),
    crane::shared_array<unsigned long long>{}};
[[clang::no_destroy]] constinit crane::shared_array<bool>::fixed<3> crane_baked_table_c8c1801e8579_b3{
    true, false, true};
constinit const void *const crane_baked_table_c8c1801e8579_blocks[] = {
    &crane_baked_table_c8c1801e8579_b2, &crane_baked_table_c8c1801e8579_b3};
constinit const std::uint64_t crane_baked_table_c8c1801e8579_words[] = {
    0,                     // no nodes
    2, 0, 2488, 2, 1, 17,  // the value: {b2, b3}
};
constinit const crane::bake::image crane_baked_table_c8c1801e8579{
    crane_baked_table_c8c1801e8579_words, 7,
    crane_baked_table_c8c1801e8579_blocks, 2, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_big_43cf8fb6d90e.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const std::uint64_t crane_baked_big_43cf8fb6d90e_words[] = {
    1, 17,          // BakedConstants::tree: #0 to #16
    0,              // #0 Leaf
    1, 0, 1, 0,     // #1 Node{l = #0, x = 1, r = #0}
    1, 1, 2, 1,     // #2 Node{l = #1, x = 2, r = #1}
    1, 2, 3, 2,     // #3 Node{l = #2, x = 3, r = #2}
    1, 3, 4, 3,     // #4 Node{l = #3, x = 4, r = #3}
    1, 4, 5, 4,     // #5 Node{l = #4, x = 5, r = #4}
    1, 5, 6, 5,     // #6 Node{l = #5, x = 6, r = #5}
    1, 6, 7, 6,     // #7 Node{l = #6, x = 7, r = #6}
    1, 7, 8, 7,     // #8 Node{l = #7, x = 8, r = #7}
    1, 8, 9, 8,     // #9 Node{l = #8, x = 9, r = #8}
    1, 9, 10, 9,    // #10 Node{l = #9, x = 10, r = #9}
    1, 10, 11, 10,  // #11 Node{l = #10, x = 11, r = #10}
    1, 11, 12, 11,  // #12 Node{l = #11, x = 12, r = #11}
    1, 12, 13, 12,  // #13 Node{l = #12, x = 13, r = #12}
    1, 13, 14, 13,  // #14 Node{l = #13, x = 14, r = #13}
    1, 14, 15, 14,  // #15 Node{l = #14, x = 15, r = #14}
    1, 15, 16, 15,  // #16 Node{l = #15, x = 16, r = #15}
    0,              // end of the nodes
    16,             // the value: #16
};
constinit const crane::bake::image crane_baked_big_43cf8fb6d90e{
    crane_baked_big_43cf8fb6d90e_words, 69, nullptr, 0, nullptr, 0};

// Baked by crane::bake: the value of crane_baked_entries_a4d00e69f151.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const char crane_baked_entries_a4d00e69f151_text0[] = "first";
constinit const std::string_view crane_baked_entries_a4d00e69f151_text[] = {
    std::string_view(crane_baked_entries_a4d00e69f151_text0, 5)};
constinit const std::uint64_t crane_baked_entries_a4d00e69f151_words[] = {
    2, 3,              // BakedConstants::tree: #0 to #2
    0,                 // #0 Leaf
    1, 0, 1, 0,        // #1 Node{l = #0, x = 1, r = #0}
    1, 1, 2, 1,        // #2 Node{l = #1, x = 2, r = #1}
    1, 3,              // List<BakedConstants::entry>: #3 to #5
    0,                 // #3 Nil
    // #4 Cons{a = entry{name = "", weight = nullopt, label = #0}, l = #3}
    1, 0, 0, 0, 3,
    // #5 Cons{a = entry{name = "first", weight = 7, label = #2}, l = #4}
    1, 5, 1, 7, 2, 4,
    0,                 // end of the nodes
    5,                 // the value: #5
};
constinit const crane::bake::image crane_baked_entries_a4d00e69f151{
    crane_baked_entries_a4d00e69f151_words, 27, nullptr, 0,
    crane_baked_entries_a4d00e69f151_text, 1};
