#ifndef INCLUDED_ATOMIC_INCLUDE
#define INCLUDED_ATOMIC_INCLUDE

#include <utility>
#include <cstdint>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_variant.h"
#include "shared_variant.h"
#include "rc.h"





struct AtomicInclude {
struct tree {
  // TYPES
struct Leaf {

};
struct Node {
crane::shared_box<tree> l;
crane::shared_box<tree> r;
};
using variant_t = crane::shared_variant<Leaf, Node>;
private:
  // DATA
variant_t v_;
public:
  // CREATORS
tree() {}
explicit tree(Leaf _v) : v_(_v) {}
explicit tree(Node _v) : v_(std::move(_v)) {}
static tree leaf() {
return tree(Leaf{});}
static tree node(tree l, tree r) {
return tree(Node{crane::shared_box<tree>::make(std::move(l)),
crane::shared_box<tree>::make(std::move(r))});}
  // MANIPULATORS
inline variant_t& v_mut() {
return v_;}
  // ACCESSORS
const variant_t& v() const {
return v_;}
};template <typename T1, typename
F1>static T1 tree_rect(T1 f, F1&& f0, const tree& t){if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
return f;
} else {
const auto& [l0, r0] = crane::get<typename tree::Node>(t.v());
return f0(*l0, tree_rect<T1>(f, f0, *l0), *r0, tree_rect<T1>(f, f0, *r0));
}}template <typename T1, typename
F1>static T1 tree_rec(T1 f, F1&& f0, const tree& t){return tree_rect<T1>(std::move(f),
f0, t);}static uint64_t size(const tree& t);
static inline const uint64_t sample = size(tree::node(tree::node(tree::leaf(), tree::leaf()), tree::leaf()));
};

#endif // INCLUDED_ATOMIC_INCLUDE
