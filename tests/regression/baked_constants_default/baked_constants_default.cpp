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
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_6bda686fed62_b0{0ULL,1ULL,2ULL,3ULL,4ULL,5ULL,6ULL,7ULL,8ULL,9ULL};
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_6bda686fed62_b1{0ULL,3ULL,6ULL,9ULL,12ULL,15ULL,18ULL,21ULL,24ULL,27ULL};
[[clang::no_destroy]] constinit crane::shared_array<crane::shared_array<unsigned long long>>::fixed<4> crane_baked_table_6bda686fed62_b2{crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b0),crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b1),crane::shared_array<unsigned long long>::of_static(crane_baked_table_6bda686fed62_b1),crane::shared_array<unsigned long long>{}};
[[clang::no_destroy]] constinit crane::shared_array<bool>::fixed<3> crane_baked_table_6bda686fed62_b3{true,false,true};
constinit const void *const crane_baked_table_6bda686fed62_blocks[] = {&crane_baked_table_6bda686fed62_b2,&crane_baked_table_6bda686fed62_b3};
constinit const std::uint64_t crane_baked_table_6bda686fed62_words[] = {0x2u,0x0u,0x9b8u,0x2u,0x1u,0x11u};
constinit const crane::bake::image crane_baked_table_6bda686fed62{crane_baked_table_6bda686fed62_words, 6, crane_baked_table_6bda686fed62_blocks, 2};

// Baked by crane::bake: the value of crane_baked_big_6a150784210f.
constinit const void *const crane_baked_big_6a150784210f_blocks[] = {nullptr};
constinit const std::uint64_t crane_baked_big_6a150784210f_words[] = {0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,
0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,
0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,
0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,0x0u,0x1u,
0x0u,0x0u,0x1u,0x0u,0x0u,0x2u,0x0u,0x1u,
0x0u,0x0u,0x1u,0x0u,0x0u,0x3u,0x0u,0x1u,
0x10u,0x2u,0x11u,0x4u,0x0u,0x1u,0xfu,0x3u,
0x12u,0x5u,0x0u,0x1u,0xeu,0x4u,0x13u,0x6u,
0x0u,0x1u,0xdu,0x5u,0x14u,0x7u,0x0u,0x1u,
0xcu,0x6u,0x15u,0x8u,0x0u,0x1u,0xbu,0x7u,
0x16u,0x9u,0x0u,0x1u,0xau,0x8u,0x17u,0xau,
0x0u,0x1u,0x9u,0x9u,0x18u,0xbu,0x0u,0x1u,
0x8u,0xau,0x19u,0xcu,0x0u,0x1u,0x7u,0xbu,
0x1au,0xdu,0x0u,0x1u,0x6u,0xcu,0x1bu,0xeu,
0x0u,0x1u,0x5u,0xdu,0x1cu,0xfu,0x0u,0x1u,
0x4u,0xeu,0x1du,0x10u,0x0u,0x1u,0x3u,0xfu,
0x1eu};
constinit const crane::bake::image crane_baked_big_6a150784210f{crane_baked_big_6a150784210f_words, 129, crane_baked_big_6a150784210f_blocks, 0};

// Baked by crane::bake: the value of crane_baked_entries_9913efaaf321.
constinit const void *const crane_baked_entries_9913efaaf321_blocks[] = {nullptr};
constinit const std::uint64_t crane_baked_entries_9913efaaf321_words[] = {0x0u,0x1u,0x0u,0x0u,0x5u,0x7473726966u,0x1u,0x7u,
0x0u,0x1u,0x0u,0x1u,0x0u,0x0u,0x1u,0x0u,
0x0u,0x2u,0x0u,0x1u,0x0u,0x0u,0x1u,0x0u,
0x0u,0x0u,0x1u,0x0u,0x0u,0x0u,0x0u,0x0u,
0x0u,0x0u,0x0u};
constinit const crane::bake::image crane_baked_entries_9913efaaf321{crane_baked_entries_9913efaaf321_words, 35, crane_baked_entries_9913efaaf321_blocks, 0};
