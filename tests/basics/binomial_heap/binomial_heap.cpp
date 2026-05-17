#include "binomial_heap.h"

BinomialHeap::tree BinomialHeap::smash(const BinomialHeap::tree &t,
                                       const BinomialHeap::tree &u) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
    const auto &[a0, a1, a2] =
        std::get<typename BinomialHeap::tree::Node>(t.v());
    auto &&_sv = *a2;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv.v())) {
      return tree::leaf();
    } else {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(u.v())) {
        const auto &[a01, a11, a21] =
            std::get<typename BinomialHeap::tree::Node>(u.v());
        auto &&_sv = *a21;
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                _sv.v())) {
          return tree::leaf();
        } else {
          if (a01 < a0) {
            return tree::node(a0, tree::node(a01, *a11, *a1), tree::leaf());
          } else {
            return tree::node(a01, tree::node(a0, *a1, *a11), tree::leaf());
          }
        }
      } else {
        return tree::leaf();
      }
    }
  } else {
    return tree::leaf();
  }
}

List<BinomialHeap::tree> BinomialHeap::carry(const List<BinomialHeap::tree> &q,
                                             BinomialHeap::tree t) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v_mut())) {
      return List<BinomialHeap::tree>::cons(t, List<BinomialHeap::tree>::nil());
    } else {
      return List<BinomialHeap::tree>::nil();
    }
  } else {
    const auto &[a0, a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(a0.v())) {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(
              t.v_mut())) {
        return List<BinomialHeap::tree>::cons(tree::leaf(),
                                              carry(*a1, smash(t, a0)));
      } else {
        return List<BinomialHeap::tree>::cons(a0, *a1);
      }
    } else {
      return List<BinomialHeap::tree>::cons(std::move(t), *a1);
    }
  }
}

BinomialHeap::priqueue BinomialHeap::insert(unsigned int x,
                                            const List<BinomialHeap::tree> &q) {
  return carry(q, tree::node(x, tree::leaf(), tree::leaf()));
}

BinomialHeap::priqueue BinomialHeap::join(const List<BinomialHeap::tree> &p,
                                          const List<BinomialHeap::tree> &q,
                                          BinomialHeap::tree c) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(p.v())) {
    return carry(q, std::move(c));
  } else {
    const auto &[a0, a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(p.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(a0.v())) {
      if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(
              q.v())) {
        return carry(p, std::move(c));
      } else {
        const auto &[a01, a11] =
            std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                a01.v())) {
          return List<BinomialHeap::tree>::cons(
              std::move(c), join(*a1, *a11, smash(a0, a01)));
        } else {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c.v_mut())) {
            return List<BinomialHeap::tree>::cons(
                tree::leaf(), join(*a1, *a11, smash(c, a0)));
          } else {
            return List<BinomialHeap::tree>::cons(
                a0, join(*a1, *a11, tree::leaf()));
          }
        }
      }
    } else {
      if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(
              q.v())) {
        return carry(p, std::move(c));
      } else {
        const auto &[a01, a11] =
            std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                a01.v())) {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c.v_mut())) {
            return List<BinomialHeap::tree>::cons(
                tree::leaf(), join(*a1, *a11, smash(c, a01)));
          } else {
            return List<BinomialHeap::tree>::cons(
                a01, join(*a1, *a11, tree::leaf()));
          }
        } else {
          return List<BinomialHeap::tree>::cons(std::move(c),
                                                join(*a1, *a11, tree::leaf()));
        }
      }
    }
  }
}

BinomialHeap::priqueue
BinomialHeap::heap_delete_max(const BinomialHeap::tree &t) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
    const auto &[a0, a1, a2] =
        std::get<typename BinomialHeap::tree::Node>(t.v());
    BinomialHeap::tree a1_value = *a1;
    BinomialHeap::tree a2_value = *a2;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(
            a2_value.v())) {
      return List<BinomialHeap::tree>::nil();
    } else {
      return unzip(a1_value, [](List<BinomialHeap::tree> u) { return u; });
    }
  } else {
    return List<BinomialHeap::tree>::nil();
  }
}

BinomialHeap::key
BinomialHeap::find_max_helper(unsigned int current,
                              const List<BinomialHeap::tree> &q) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    return current;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(a0.v())) {
      const auto &[a00, a10, a20] =
          std::get<typename BinomialHeap::tree::Node>(a0.v());
      return find_max_helper((current < a00 ? a00 : current), *a1);
    } else {
      return find_max_helper(current, *a1);
    }
  }
}

std::optional<BinomialHeap::key>
BinomialHeap::find_max(const List<BinomialHeap::tree> &q) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(a0.v())) {
      const auto &[a00, a10, a20] =
          std::get<typename BinomialHeap::tree::Node>(a0.v());
      return std::make_optional<unsigned int>(find_max_helper(a00, *a1));
    } else {
      return find_max(*a1);
    }
  }
}

std::pair<BinomialHeap::priqueue, BinomialHeap::priqueue>
BinomialHeap::delete_max_aux(unsigned int m,
                             const List<BinomialHeap::tree> &p) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(p.v())) {
    return std::make_pair(List<BinomialHeap::tree>::nil(),
                          List<BinomialHeap::tree>::nil());
  } else {
    const auto &[a0, a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(p.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(a0.v())) {
      const auto &[a00, a10, a20] =
          std::get<typename BinomialHeap::tree::Node>(a0.v());
      auto &&_sv = *a20;
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv.v())) {
        return std::make_pair(List<BinomialHeap::tree>::nil(),
                              List<BinomialHeap::tree>::nil());
      } else {
        if (a00 < m) {
          auto _cs = delete_max_aux(m, *a1);
          const List<BinomialHeap::tree> &j = _cs.first;
          const List<BinomialHeap::tree> &k = _cs.second;
          return std::make_pair(List<BinomialHeap::tree>::cons(
                                    tree::node(a00, *a10, tree::leaf()), j),
                                k);
        } else {
          return std::make_pair(
              List<BinomialHeap::tree>::cons(tree::leaf(), *a1),
              heap_delete_max(tree::node(a00, *a10, tree::leaf())));
        }
      }
    } else {
      auto _cs = delete_max_aux(m, *a1);
      const List<BinomialHeap::tree> &j = _cs.first;
      const List<BinomialHeap::tree> &k = _cs.second;
      return std::make_pair(List<BinomialHeap::tree>::cons(tree::leaf(), j), k);
    }
  }
}

std::optional<std::pair<BinomialHeap::key, BinomialHeap::priqueue>>
BinomialHeap::delete_max(const List<BinomialHeap::tree> &q) {
  auto _cs = find_max(q);
  if (_cs.has_value()) {
    const unsigned int &m = *_cs;
    auto _cs1 = delete_max_aux(m, q);
    const List<BinomialHeap::tree> &p_ = _cs1.first;
    const List<BinomialHeap::tree> &q_ = _cs1.second;
    return std::make_optional<
        std::pair<unsigned int, List<BinomialHeap::tree>>>(
        std::make_pair(m, join(p_, q_, tree::leaf())));
  } else {
    return std::optional<std::pair<unsigned int, List<BinomialHeap::tree>>>();
  }
}

BinomialHeap::priqueue BinomialHeap::merge(const List<BinomialHeap::tree> &p,
                                           const List<BinomialHeap::tree> &q) {
  return join(p, q, tree::leaf());
}

BinomialHeap::priqueue BinomialHeap::insert_list(const List<unsigned int> &l,
                                                 List<BinomialHeap::tree> q) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return q;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    return insert_list(*a1, insert(a0, std::move(q)));
  }
}

List<unsigned int> BinomialHeap::make_list(unsigned int n,
                                           List<unsigned int> l) {
  if (n <= 0) {
    return List<unsigned int>::cons(0u, std::move(l));
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return List<unsigned int>::cons(1u, std::move(l));
    } else {
      unsigned int n1 = n0 - 1;
      return make_list(n1,
                       List<unsigned int>::cons(((n1 + 1) + 1), std::move(l)));
    }
  }
}

BinomialHeap::key BinomialHeap::help(const List<BinomialHeap::tree> &c) {
  auto _cs = delete_max(c);
  if (_cs.has_value()) {
    const std::pair<unsigned int, List<BinomialHeap::tree>> &p = *_cs;
    const unsigned int &k = p.first;
    const List<BinomialHeap::tree> &_x = p.second;
    return k;
  } else {
    return 0u;
  }
}
