#include "shared_variant_reuse.h"

SharedVariantReuse::tree
SharedVariantReuse::insert(uint64_t k, uint64_t v, SharedVariantReuse::tree t) {
  if (t.v().index() == 1) {
    if (t.v().unique()) {
      SharedVariantReuse::tree l = std::move(
          *crane::get<typename SharedVariantReuse::tree::Node>(t.v_mut()).a0);
      uint64_t k_ = std::move(
          crane::get<typename SharedVariantReuse::tree::Node>(t.v_mut()).a1);
      uint64_t v_ = std::move(
          crane::get<typename SharedVariantReuse::tree::Node>(t.v_mut()).a2);
      SharedVariantReuse::tree r = std::move(
          *crane::get<typename SharedVariantReuse::tree::Node>(t.v_mut()).a3);
      if (k < k_) {
        return tree::node_crane_reuse(std::move(t), insert(k, v, std::move(l)),
                                      k_, v_, std::move(r));
      } else {
        if (k_ < k) {
          return tree::node_crane_reuse(std::move(t), std::move(l), k_, v_,
                                        insert(k, v, std::move(r)));
        } else {
          return tree::node_crane_reuse(std::move(t), std::move(l), k, v,
                                        std::move(r));
        }
      }
    } else {
      if (crane::holds_alternative<typename SharedVariantReuse::tree::Leaf>(
              t.v())) {
        return tree::node(tree::leaf(), k, v, tree::leaf());
      } else {
        const auto &[a0, a1, a2, a3] =
            crane::get<typename SharedVariantReuse::tree::Node>(t.v());
        if (k < a1) {
          return tree::node(insert(k, v, *a0), a1, a2, *a3);
        } else {
          if (a1 < k) {
            return tree::node(*a0, a1, a2, insert(k, v, *a3));
          } else {
            return tree::node(*a0, k, v, *a3);
          }
        }
      }
    }
  } else {
    if (crane::holds_alternative<typename SharedVariantReuse::tree::Leaf>(
            t.v())) {
      return tree::node(tree::leaf(), k, v, tree::leaf());
    } else {
      const auto &[a0, a1, a2, a3] =
          crane::get<typename SharedVariantReuse::tree::Node>(t.v());
      if (k < a1) {
        return tree::node(insert(k, v, *a0), a1, a2, *a3);
      } else {
        if (a1 < k) {
          return tree::node(*a0, a1, a2, insert(k, v, *a3));
        } else {
          return tree::node(*a0, k, v, *a3);
        }
      }
    }
  }
}

SharedVariantReuse::lst SharedVariantReuse::bump(SharedVariantReuse::lst l) {
  if (l.v().index() == 1) {
    if (l.v().unique()) {
      uint64_t x = std::move(
          crane::get<typename SharedVariantReuse::lst::Cons>(l.v_mut()).a0);
      SharedVariantReuse::lst xs = std::move(
          *crane::get<typename SharedVariantReuse::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(std::move(l), (x + 1), bump(std::move(xs)));
    } else {
      if (crane::holds_alternative<typename SharedVariantReuse::lst::Nil>(
              l.v())) {
        return lst::nil();
      } else {
        const auto &[a0, a1] =
            crane::get<typename SharedVariantReuse::lst::Cons>(l.v());
        return lst::cons((a0 + 1), bump(*a1));
      }
    }
  } else {
    if (crane::holds_alternative<typename SharedVariantReuse::lst::Nil>(
            l.v())) {
      return lst::nil();
    } else {
      const auto &[a0, a1] =
          crane::get<typename SharedVariantReuse::lst::Cons>(l.v());
      return lst::cons((a0 + 1), bump(*a1));
    }
  }
}
