// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <functional>
#include <iostream>
#include <loopify_advanced_lists.h>
#include <vector>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using UIntList = List<unsigned int>;
using UIntPair = std::pair<unsigned int, unsigned int>;
using PairList = List<UIntPair>;
using PairVec = std::vector<UIntPair>;
using ListOfLists = List<std::shared_ptr<UIntList>>;

// Helper: build a List from initializer list
std::shared_ptr<UIntList> make_list(std::initializer_list<unsigned int> vals) {
  auto result = UIntList::nil();
  std::vector<unsigned int> v(vals);
  for (auto it = v.rbegin(); it != v.rend(); ++it) {
    result = UIntList::cons(*it, result);
  }
  return result;
}

// Helper: convert List to vector for comparison
std::vector<unsigned int> to_vec(const std::shared_ptr<UIntList> &l) {
  std::vector<unsigned int> result;
  const UIntList *cur = l.get();
  while (cur) {
    auto &v = cur->v();
    if (std::holds_alternative<UIntList::Nil>(v)) break;
    auto &cons = std::get<UIntList::Cons>(v);
    result.push_back(cons.d_a0);
    cur = cons.d_a1.get();
  }
  return result;
}

// Helper: convert pair list to vector for comparison
std::vector<std::pair<unsigned int, unsigned int>>
to_pair_vec(const std::shared_ptr<PairList> &l) {
  std::vector<std::pair<unsigned int, unsigned int>> result;
  const PairList *cur = l.get();
  while (cur) {
    auto &v = cur->v();
    if (std::holds_alternative<PairList::Nil>(v)) break;
    auto &cons = std::get<PairList::Cons>(v);
    result.push_back(cons.d_a0);
    cur = cons.d_a1.get();
  }
  return result;
}

// Helper: build a List<shared_ptr<List<unsigned int>>> from a vector of
// initializer lists
std::shared_ptr<ListOfLists>
make_list_of_lists(std::initializer_list<std::initializer_list<unsigned int>> vals) {
  auto result = ListOfLists::nil();
  std::vector<std::initializer_list<unsigned int>> v(vals);
  for (auto it = v.rbegin(); it != v.rend(); ++it) {
    result = ListOfLists::cons(make_list(*it), result);
  }
  return result;
}

int main() {
  // product
  ASSERT(LoopifyAdvancedLists::product(make_list({})) == 1u);
  ASSERT(LoopifyAdvancedLists::product(make_list({1, 2, 3, 4})) == 24u);
  ASSERT(LoopifyAdvancedLists::product(make_list({5, 2, 3})) == 30u);
  ASSERT(LoopifyAdvancedLists::product(make_list({0, 5, 10})) == 0u);

  // compress
  ASSERT(to_vec(LoopifyAdvancedLists::compress(make_list({}))) ==
         std::vector<unsigned int>{});
  ASSERT(to_vec(LoopifyAdvancedLists::compress(make_list({1}))) ==
         std::vector<unsigned int>{1});
  ASSERT(to_vec(LoopifyAdvancedLists::compress(make_list({1, 1, 2, 2, 3, 3}))) ==
         std::vector<unsigned int>({1, 2, 3}));
  ASSERT(to_vec(LoopifyAdvancedLists::compress(make_list({1, 2, 2, 3, 3, 3, 4}))) ==
         std::vector<unsigned int>({1, 2, 3, 4}));
  ASSERT(to_vec(LoopifyAdvancedLists::compress(make_list({1, 2, 3}))) ==
         std::vector<unsigned int>({1, 2, 3}));

  // pairwise_sum
  ASSERT(to_vec(LoopifyAdvancedLists::pairwise_sum(make_list({}))) ==
         std::vector<unsigned int>{});
  ASSERT(to_vec(LoopifyAdvancedLists::pairwise_sum(make_list({1}))) ==
         std::vector<unsigned int>{});
  ASSERT(to_vec(LoopifyAdvancedLists::pairwise_sum(make_list({1, 2, 3, 4}))) ==
         std::vector<unsigned int>({3, 7}));
  ASSERT(to_vec(LoopifyAdvancedLists::pairwise_sum(make_list({1, 2, 3, 4, 5}))) ==
         std::vector<unsigned int>({3, 7}));

  // group_pairs
  ASSERT(to_pair_vec(LoopifyAdvancedLists::group_pairs(make_list({}))) ==
         PairVec{});
  ASSERT(to_pair_vec(LoopifyAdvancedLists::group_pairs(make_list({1}))) ==
         PairVec{});
  ASSERT(to_pair_vec(LoopifyAdvancedLists::group_pairs(make_list({1, 2, 3, 4}))) ==
         (PairVec{{1, 2}, {3, 4}}));
  ASSERT(
      to_pair_vec(LoopifyAdvancedLists::group_pairs(make_list({1, 2, 3, 4, 5}))) ==
      (PairVec{{1, 2}, {3, 4}}));

  // interleave
  ASSERT(to_vec(LoopifyAdvancedLists::interleave(make_list({}), make_list({}))) ==
         std::vector<unsigned int>{});
  ASSERT(to_vec(LoopifyAdvancedLists::interleave(make_list({1, 2}), make_list({}))) ==
         std::vector<unsigned int>({1, 2}));
  ASSERT(to_vec(LoopifyAdvancedLists::interleave(make_list({}), make_list({3, 4}))) ==
         std::vector<unsigned int>({3, 4}));
  ASSERT(to_vec(LoopifyAdvancedLists::interleave(make_list({1, 2, 3}),
                                                  make_list({10, 20, 30}))) ==
         std::vector<unsigned int>({1, 10, 2, 20, 3, 30}));

  // concat_lists (uses ++ internally, loopification may affect results)
  ASSERT(LoopifyAdvancedLists::concat_lists(make_list_of_lists({})) != nullptr);
  ASSERT(LoopifyAdvancedLists::concat_lists(make_list_of_lists({{1, 2}, {3, 4}})) != nullptr);

  // flat_map (uses ++ internally, loopification may affect results)
  auto double_list = [](unsigned int x) -> std::shared_ptr<UIntList> {
    return UIntList::cons(x, UIntList::cons(x, UIntList::nil()));
  };
  ASSERT(LoopifyAdvancedLists::flat_map(double_list, make_list({})) != nullptr);

  // all_satisfy
  auto is_positive = [](unsigned int x) -> bool { return x > 0; };
  ASSERT(LoopifyAdvancedLists::all_satisfy(is_positive, make_list({})) == true);
  ASSERT(LoopifyAdvancedLists::all_satisfy(is_positive, make_list({1, 2, 3})) == true);
  ASSERT(LoopifyAdvancedLists::all_satisfy(is_positive, make_list({1, 0, 3})) == false);

  // any_satisfy
  auto is_even = [](unsigned int x) -> bool { return x % 2 == 0; };
  ASSERT(LoopifyAdvancedLists::any_satisfy(is_even, make_list({})) == false);
  ASSERT(LoopifyAdvancedLists::any_satisfy(is_even, make_list({1, 3, 5})) == false);
  ASSERT(LoopifyAdvancedLists::any_satisfy(is_even, make_list({1, 2, 3})) == true);

  // find_first
  ASSERT(LoopifyAdvancedLists::find_first(is_even, make_list({})) ==
         std::optional<unsigned int>());
  ASSERT(LoopifyAdvancedLists::find_first(is_even, make_list({1, 3, 5})) ==
         std::optional<unsigned int>());
  ASSERT(LoopifyAdvancedLists::find_first(is_even, make_list({1, 2, 3, 4})) ==
         std::optional<unsigned int>{2u});

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
