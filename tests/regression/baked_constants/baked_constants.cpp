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
    return ((UINT64_C(1) + size(*l0)) + size(*r0));
  }
}

uint64_t BakedConstants::sum_tree(const BakedConstants::tree &t) {
  if (crane::holds_alternative<typename BakedConstants::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[l0, x0, r0] =
        crane::get<typename BakedConstants::tree::Node>(t.v());
    return ((sum_tree(*l0) + x0) + sum_tree(*r0));
  }
}

/// Baked: a table of rows, two of them the same row.
crane::shared_array<uint64_t> BakedConstants::row(uint64_t k) {
  return vec_of_list<uint64_t>(
      ListDef::seq(UINT64_C(0), UINT64_C(10)).template map<uint64_t>(
          [=](uint64_t i) { return (i * k); }));
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
          return (w + acc);
        } else {
          return acc;
        }
      },
      UINT64_C(0));
}

/// What cannot be baked.
uint64_t BakedConstants::twice(uint64_t n) { return (n + n); }

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
    0ULL, 1ULL, 2ULL, 3ULL, 4ULL, 5ULL, 6ULL, 7ULL, 8ULL, 9ULL};
[[clang::no_destroy]] constinit crane::shared_array<unsigned long long>::fixed<10> crane_baked_table_c8c1801e8579_b1{
    0ULL, 3ULL, 6ULL, 9ULL, 12ULL, 15ULL, 18ULL, 21ULL, 24ULL, 27ULL};
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
    0x2u, 0x0u, 0x9b8u, 0x2u, 0x1u, 0x11u};
constinit const crane::bake::image crane_baked_table_c8c1801e8579{
    crane_baked_table_c8c1801e8579_words, 6,
    crane_baked_table_c8c1801e8579_blocks, 2};

// Baked by crane::bake: the value of crane_baked_big_43cf8fb6d90e.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const void *const crane_baked_big_43cf8fb6d90e_blocks[] = {nullptr};
constinit const std::uint64_t crane_baked_big_43cf8fb6d90e_words[] = {
    0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u,
    0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u,
    0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x1u, 0x0u, 0x0u, 0x1u, 0x0u,
    0x0u, 0x2u, 0x10u, 0x3u, 0xfu, 0x4u, 0xeu, 0x5u, 0xdu, 0x6u, 0xcu, 0x7u,
    0xbu, 0x8u, 0xau, 0x9u, 0x9u, 0xau, 0x8u, 0xbu, 0x7u, 0xcu, 0x6u, 0xdu,
    0x5u, 0xeu, 0x4u, 0xfu, 0x3u, 0x10u, 0x2u};
constinit const crane::bake::image crane_baked_big_43cf8fb6d90e{
    crane_baked_big_43cf8fb6d90e_words, 67, crane_baked_big_43cf8fb6d90e_blocks,
    0};

// Baked by crane::bake: the value of crane_baked_entries_a4d00e69f151.
static_assert(crane::bake::data_model == 0x80408080402u,
              "crane::bake: baked on a host with other scalar widths");
constinit const void *const crane_baked_entries_a4d00e69f151_blocks[] = {
    nullptr};
constinit const std::uint64_t crane_baked_entries_a4d00e69f151_words[] = {
    0x0u, 0x1u, 0x0u, 0x0u, 0x5u, 0x7473726966u, 0x1u, 0x7u, 0x0u, 0x1u, 0x0u,
    0x1u, 0x0u, 0x0u, 0x1u, 0x0u, 0x0u, 0x2u, 0x2u, 0x0u, 0x1u, 0x0u, 0x0u,
    0x0u, 0x0u, 0x0u, 0x0u, 0x0u, 0x0u};
constinit const crane::bake::image crane_baked_entries_a4d00e69f151{
    crane_baked_entries_a4d00e69f151_words, 29,
    crane_baked_entries_a4d00e69f151_blocks, 0};
