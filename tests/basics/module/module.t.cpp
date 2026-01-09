// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// Stub implementations for missing functions
// These are needed because TestCompile only extracts what's referenced from mymap

std::shared_ptr<typename Comparison::comparison> Comparison::Eq::make() {
  return std::make_shared<comparison>(Eq{});
}

std::shared_ptr<typename Comparison::comparison> Comparison::Lt::make() {
  return std::make_shared<comparison>(Lt{});
}

std::shared_ptr<typename Comparison::comparison> Comparison::Gt::make() {
  return std::make_shared<comparison>(Gt{});
}

template <OrderedType K, BaseType V>
std::shared_ptr<typename MakeMap<K, V>::Tree::tree> MakeMap<K, V>::Tree::Empty::make() {
  return std::make_shared<tree>(Empty{});
}

template <OrderedType K, BaseType V>
std::shared_ptr<typename MakeMap<K, V>::Tree::tree> MakeMap<K, V>::Tree::Node::make(
    std::shared_ptr<tree> _a0, K::t _a1, V::t _a2, std::shared_ptr<tree> _a3) {
  return std::make_shared<tree>(Node{_a0, _a1, _a2, _a3});
}

template <OrderedType K, BaseType V>
typename MakeMap<K, V>::t MakeMap<K, V>::add(const typename K::t k, const typename V::t v,
                                             const std::shared_ptr<typename Tree::tree> m) {
  return std::visit(
      Overloaded{
          [&](const Tree::Empty&) -> t {
            return Tree::Node::make(Tree::Empty::make(), k, v, Tree::Empty::make());
          },
          [&](const Tree::Node& node) -> t {
            auto cmp = K::compare(k, node._a1);
            return std::visit(
                Overloaded{
                    [&](const Comparison::Eq&) -> t {
                      return Tree::Node::make(node._a0, k, v, node._a3);
                    },
                    [&](const Comparison::Lt&) -> t {
                      return Tree::Node::make(add(k, v, node._a0), node._a1, node._a2, node._a3);
                    },
                    [&](const Comparison::Gt&) -> t {
                      return Tree::Node::make(node._a0, node._a1, node._a2, add(k, v, node._a3));
                    },
                },
                *cmp);
          },
      },
      *m);
}

template <OrderedType K, BaseType V>
std::optional<typename MakeMap<K, V>::value> MakeMap<K, V>::find(const typename K::t k,
                                                                   const std::shared_ptr<typename Tree::tree> m) {
  return std::visit(
      Overloaded{
          [&](const Tree::Empty&) -> std::optional<value> { return std::nullopt; },
          [&](const Tree::Node& node) -> std::optional<value> {
            auto cmp = K::compare(k, node._a1);
            return std::visit(
                Overloaded{
                    [&](const Comparison::Eq&) -> std::optional<value> { return node._a2; },
                    [&](const Comparison::Lt&) -> std::optional<value> { return find(k, node._a0); },
                    [&](const Comparison::Gt&) -> std::optional<value> { return find(k, node._a3); },
                },
                *cmp);
          },
      },
      *m);
}

// Explicit template instantiation for NatMap
template struct MakeMap<NatOrdered, NatBase>;

std::shared_ptr<typename Comparison::comparison> NatOrdered::compare(const unsigned int n,
                                                                      const unsigned int m) {
  if (n < m) return Comparison::Lt::make();
  if (n > m) return Comparison::Gt::make();
  return Comparison::Eq::make();
}

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
  // Test: NatMap.find 2 mymap   (* Should output Some 20 *)
  auto result1 = NatMap::find(2, mymap);
  ASSERT(result1.has_value());
  ASSERT(result1.value() == 20);
  std::cout << "NatMap.find(2, mymap) = ";
  if (result1.has_value()) {
    std::cout << "Some(" << result1.value() << ")" << std::endl;
  } else {
    std::cout << "None" << std::endl;
  }

  // Test: NatMap.find 4 mymap   (* Should output None *)
  auto result2 = NatMap::find(4, mymap);
  ASSERT(!result2.has_value());
  std::cout << "NatMap.find(4, mymap) = ";
  if (result2.has_value()) {
    std::cout << "Some(" << result2.value() << ")" << std::endl;
  } else {
    std::cout << "None" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "All tests passed!" << std::endl;
  }
  return testStatus;
}
