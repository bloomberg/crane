#include <binomial_heap.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) BinomialHeap::tree
BinomialHeap::smash(const BinomialHeap::tree &t, const BinomialHeap::tree &u) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename BinomialHeap::tree::Node>(t.v());
    auto &&_sv = *(d_a2);
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv.v())) {
      return tree::leaf();
    } else {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(u.v())) {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename BinomialHeap::tree::Node>(u.v());
        auto &&_sv = *(d_a21);
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                _sv.v())) {
          return tree::leaf();
        } else {
          if (d_a01 < d_a0) {
            return tree::node(d_a0, tree::node(d_a01, *(d_a11), *(d_a1)),
                              tree::leaf());
          } else {
            return tree::node(d_a01, tree::node(d_a0, *(d_a1), *(d_a11)),
                              tree::leaf());
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

__attribute__((pure)) List<BinomialHeap::tree>
BinomialHeap::carry(const List<BinomialHeap::tree> &q, BinomialHeap::tree t) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
      return List<BinomialHeap::tree>::cons(t, List<BinomialHeap::tree>::nil());
    } else {
      return List<BinomialHeap::tree>::nil();
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(d_a0.v())) {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
        return List<BinomialHeap::tree>::cons(tree::leaf(),
                                              carry(*(d_a1), smash(t, d_a0)));
      } else {
        return List<BinomialHeap::tree>::cons(d_a0, *(d_a1));
      }
    } else {
      return List<BinomialHeap::tree>::cons(t, *(d_a1));
    }
  }
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::insert(unsigned int x, const List<BinomialHeap::tree> &q) {
  return carry(q, tree::node(x, tree::leaf(), tree::leaf()));
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::join(const List<BinomialHeap::tree> &p,
                   const List<BinomialHeap::tree> &q, BinomialHeap::tree c) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(p.v())) {
    return carry(q, c);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(p.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(d_a0.v())) {
      if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(
              q.v())) {
        return carry(p, c);
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                d_a01.v())) {
          return List<BinomialHeap::tree>::cons(
              c, join(*(d_a1), *(d_a11), smash(d_a0, d_a01)));
        } else {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c.v())) {
            return List<BinomialHeap::tree>::cons(
                tree::leaf(), join(*(d_a1), *(d_a11), smash(c, d_a0)));
          } else {
            return List<BinomialHeap::tree>::cons(
                d_a0, join(*(d_a1), *(d_a11), tree::leaf()));
          }
        }
      }
    } else {
      if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(
              q.v())) {
        return carry(p, c);
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                d_a01.v())) {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c.v())) {
            return List<BinomialHeap::tree>::cons(
                tree::leaf(), join(*(d_a1), *(d_a11), smash(c, d_a01)));
          } else {
            return List<BinomialHeap::tree>::cons(
                d_a01, join(*(d_a1), *(d_a11), tree::leaf()));
          }
        } else {
          return List<BinomialHeap::tree>::cons(
              c, join(*(d_a1), *(d_a11), tree::leaf()));
        }
      }
    }
  }
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::heap_delete_max(const BinomialHeap::tree &t) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename BinomialHeap::tree::Node>(t.v());
    BinomialHeap::tree d_a1_value = *(d_a1);
    BinomialHeap::tree d_a2_value = *(d_a2);
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(
            d_a2_value.v())) {
      return List<BinomialHeap::tree>::nil();
    } else {
      return unzip(d_a1_value, [](List<BinomialHeap::tree> u) { return u; });
    }
  } else {
    return List<BinomialHeap::tree>::nil();
  }
}

__attribute__((pure)) BinomialHeap::key
BinomialHeap::find_max_helper(unsigned int current,
                              const List<BinomialHeap::tree> &q) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    return current;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(d_a0.v())) {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename BinomialHeap::tree::Node>(d_a0.v());
      return find_max_helper(
          [&]() -> unsigned int {
            if (current < d_a00) {
              return d_a00;
            } else {
              return current;
            }
          }(),
          *(d_a1));
    } else {
      return find_max_helper(current, *(d_a1));
    }
  }
}

__attribute__((pure)) std::optional<BinomialHeap::key>
BinomialHeap::find_max(const List<BinomialHeap::tree> &q) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(q.v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(q.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(d_a0.v())) {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename BinomialHeap::tree::Node>(d_a0.v());
      return std::make_optional<unsigned int>(find_max_helper(d_a00, *(d_a1)));
    } else {
      return find_max(*(d_a1));
    }
  }
}

__attribute__((pure)) std::pair<BinomialHeap::priqueue, BinomialHeap::priqueue>
BinomialHeap::delete_max_aux(const unsigned int &m,
                             const List<BinomialHeap::tree> &p) {
  if (std::holds_alternative<typename List<BinomialHeap::tree>::Nil>(p.v())) {
    return std::make_pair(List<BinomialHeap::tree>::nil(),
                          List<BinomialHeap::tree>::nil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<BinomialHeap::tree>::Cons>(p.v());
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(d_a0.v())) {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename BinomialHeap::tree::Node>(d_a0.v());
      auto &&_sv = *(d_a20);
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv.v())) {
        return std::make_pair(List<BinomialHeap::tree>::nil(),
                              List<BinomialHeap::tree>::nil());
      } else {
        if (d_a00 < m) {
          auto _cs = delete_max_aux(m, *(d_a1));
          const List<BinomialHeap::tree> &j = _cs.first;
          const List<BinomialHeap::tree> &k = _cs.second;
          return std::make_pair(
              List<BinomialHeap::tree>::cons(
                  tree::node(d_a00, *(d_a10), tree::leaf()), j),
              k);
        } else {
          return std::make_pair(
              List<BinomialHeap::tree>::cons(tree::leaf(), *(d_a1)),
              heap_delete_max(tree::node(d_a00, *(d_a10), tree::leaf())));
        }
      }
    } else {
      auto _cs = delete_max_aux(m, *(d_a1));
      const List<BinomialHeap::tree> &j = _cs.first;
      const List<BinomialHeap::tree> &k = _cs.second;
      return std::make_pair(List<BinomialHeap::tree>::cons(tree::leaf(), j), k);
    }
  }
}

__attribute__((pure))
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

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::merge(const List<BinomialHeap::tree> &p,
                    const List<BinomialHeap::tree> &q) {
  return join(p, q, tree::leaf());
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::insert_list(const List<unsigned int> &l,
                          List<BinomialHeap::tree> q) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return q;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return insert_list(*(d_a1), insert(d_a0, q));
  }
}

__attribute__((pure)) List<unsigned int>
BinomialHeap::make_list(const unsigned int &n, List<unsigned int> l) {
  if (n <= 0) {
    return List<unsigned int>::cons(0u, l);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return List<unsigned int>::cons(1u, l);
    } else {
      unsigned int n1 = n0 - 1;
      return make_list(n1, List<unsigned int>::cons(((n1 + 1) + 1), l));
    }
  }
}

__attribute__((pure)) BinomialHeap::key
BinomialHeap::help(const List<BinomialHeap::tree> &c) {
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
