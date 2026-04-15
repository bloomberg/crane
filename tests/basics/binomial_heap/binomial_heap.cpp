#include <binomial_heap.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<BinomialHeap::tree>
BinomialHeap::smash(const std::shared_ptr<BinomialHeap::tree> &t,
                    const std::shared_ptr<BinomialHeap::tree> &u) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t->v())) {
    const auto &_m = *std::get_if<typename BinomialHeap::tree::Node>(&t->v());
    auto &&_sv = _m.d_a2;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv->v())) {
      return tree::leaf();
    } else {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(u->v())) {
        const auto &_m1 =
            *std::get_if<typename BinomialHeap::tree::Node>(&u->v());
        auto &&_sv = _m1.d_a2;
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                _sv->v())) {
          return tree::leaf();
        } else {
          if (_m1.d_a0 < _m.d_a0) {
            return tree::node(_m.d_a0, tree::node(_m1.d_a0, _m1.d_a1, _m.d_a1),
                              tree::leaf());
          } else {
            return tree::node(_m1.d_a0, tree::node(_m.d_a0, _m.d_a1, _m1.d_a1),
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

std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> BinomialHeap::carry(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> t) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(q->v())) {
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(t->v())) {
      return List<std::shared_ptr<BinomialHeap::tree>>::cons(
          t, List<std::shared_ptr<BinomialHeap::tree>>::nil());
    } else {
      return List<std::shared_ptr<BinomialHeap::tree>>::nil();
    }
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(
            &q->v());
    auto &&_sv = _m.d_a0;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv->v())) {
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(t->v())) {
        return List<std::shared_ptr<BinomialHeap::tree>>::cons(
            tree::leaf(), carry(_m.d_a1, smash(t, _m.d_a0)));
      } else {
        return List<std::shared_ptr<BinomialHeap::tree>>::cons(_m.d_a0,
                                                               _m.d_a1);
      }
    } else {
      return List<std::shared_ptr<BinomialHeap::tree>>::cons(t, _m.d_a1);
    }
  }
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return carry(q, tree::node(x, tree::leaf(), tree::leaf()));
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::join(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> c) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(p->v())) {
    return carry(q, std::move(c));
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(
            &p->v());
    auto &&_sv = _m.d_a0;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv->v())) {
      if (std::holds_alternative<
              typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(
              q->v())) {
        return carry(p, std::move(c));
      } else {
        const auto &_m1 = *std::get_if<
            typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(&q->v());
        auto &&_sv = _m1.d_a0;
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                _sv->v())) {
          return List<std::shared_ptr<BinomialHeap::tree>>::cons(
              c, join(_m.d_a1, _m1.d_a1, smash(_m.d_a0, _m1.d_a0)));
        } else {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c->v())) {
            return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                tree::leaf(), join(_m.d_a1, _m1.d_a1, smash(c, _m.d_a0)));
          } else {
            return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                _m.d_a0, join(_m.d_a1, _m1.d_a1, tree::leaf()));
          }
        }
      }
    } else {
      if (std::holds_alternative<
              typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(
              q->v())) {
        return carry(p, std::move(c));
      } else {
        const auto &_m1 = *std::get_if<
            typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(&q->v());
        auto &&_sv = _m1.d_a0;
        if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                _sv->v())) {
          if (std::holds_alternative<typename BinomialHeap::tree::Node>(
                  c->v())) {
            return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                tree::leaf(), join(_m.d_a1, _m1.d_a1, smash(c, _m1.d_a0)));
          } else {
            return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                _m1.d_a0, join(_m.d_a1, _m1.d_a1, tree::leaf()));
          }
        } else {
          return List<std::shared_ptr<BinomialHeap::tree>>::cons(
              c, join(_m.d_a1, _m1.d_a1, tree::leaf()));
        }
      }
    }
  }
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::heap_delete_max(const std::shared_ptr<BinomialHeap::tree> &t) {
  if (std::holds_alternative<typename BinomialHeap::tree::Node>(t->v())) {
    const auto &_m = *std::get_if<typename BinomialHeap::tree::Node>(&t->v());
    auto &&_sv = _m.d_a2;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv->v())) {
      return List<std::shared_ptr<BinomialHeap::tree>>::nil();
    } else {
      return unzip(
          _m.d_a1,
          [](std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> u) {
            return u;
          });
    }
  } else {
    return List<std::shared_ptr<BinomialHeap::tree>>::nil();
  }
}

__attribute__((pure)) BinomialHeap::key BinomialHeap::find_max_helper(
    const unsigned int current,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(q->v())) {
    return current;
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(
            &q->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename BinomialHeap::tree::Node>(&_sv0->v());
      return find_max_helper(
          [&]() -> unsigned int {
            if (current < _m0.d_a0) {
              return _m0.d_a0;
            } else {
              return current;
            }
          }(),
          _m.d_a1);
    } else {
      return find_max_helper(current, _m.d_a1);
    }
  }
}

__attribute__((pure)) std::optional<BinomialHeap::key> BinomialHeap::find_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(q->v())) {
    return std::optional<unsigned int>();
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(
            &q->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename BinomialHeap::tree::Node>(&_sv0->v());
      return std::make_optional<unsigned int>(
          find_max_helper(_m0.d_a0, _m.d_a1));
    } else {
      return find_max(_m.d_a1);
    }
  }
}

__attribute__((pure)) std::pair<BinomialHeap::priqueue, BinomialHeap::priqueue>
BinomialHeap::delete_max_aux(
    const unsigned int m,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<BinomialHeap::tree>>::Nil>(p->v())) {
    return std::make_pair(List<std::shared_ptr<BinomialHeap::tree>>::nil(),
                          List<std::shared_ptr<BinomialHeap::tree>>::nil());
  } else {
    const auto &_m =
        *std::get_if<typename List<std::shared_ptr<BinomialHeap::tree>>::Cons>(
            &p->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename BinomialHeap::tree::Node>(&_sv0->v());
      auto &&_sv = _m0.d_a2;
      if (std::holds_alternative<typename BinomialHeap::tree::Node>(_sv->v())) {
        return std::make_pair(List<std::shared_ptr<BinomialHeap::tree>>::nil(),
                              List<std::shared_ptr<BinomialHeap::tree>>::nil());
      } else {
        if (_m0.d_a0 < m) {
          auto _cs = delete_max_aux(m, _m.d_a1);
          const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &j =
              _cs.first;
          const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &k =
              _cs.second;
          return std::make_pair(
              List<std::shared_ptr<BinomialHeap::tree>>::cons(
                  tree::node(_m0.d_a0, _m0.d_a1, tree::leaf()), j),
              k);
        } else {
          return std::make_pair(
              List<std::shared_ptr<BinomialHeap::tree>>::cons(tree::leaf(),
                                                              _m.d_a1),
              heap_delete_max(tree::node(_m0.d_a0, _m0.d_a1, tree::leaf())));
        }
      }
    } else {
      auto _cs = delete_max_aux(m, _m.d_a1);
      const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &j =
          _cs.first;
      const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &k =
          _cs.second;
      return std::make_pair(
          List<std::shared_ptr<BinomialHeap::tree>>::cons(tree::leaf(), j), k);
    }
  }
}

__attribute__((pure))
std::optional<std::pair<BinomialHeap::key, BinomialHeap::priqueue>>
BinomialHeap::delete_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  auto _cs = find_max(q);
  if (_cs.has_value()) {
    const unsigned int &m = *_cs;
    auto _cs = delete_max_aux(m, q);
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p_ =
        _cs.first;
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q_ =
        _cs.second;
    return std::make_optional<
        std::pair<unsigned int,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>>(
        std::make_pair(m, join(p_, q_, tree::leaf())));
  } else {
    return std::optional<std::pair<
        unsigned int,
        std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>>();
  }
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::merge(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return join(p, q, tree::leaf());
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert_list(
    const std::shared_ptr<List<unsigned int>> &l,
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return q;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
    return insert_list(_m.d_a1, insert(_m.d_a0, std::move(q)));
  }
}

std::shared_ptr<List<unsigned int>>
BinomialHeap::make_list(const unsigned int n,
                        std::shared_ptr<List<unsigned int>> l) {
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

__attribute__((pure)) BinomialHeap::key BinomialHeap::help(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &c) {
  auto _cs = delete_max(c);
  if (_cs.has_value()) {
    const std::pair<unsigned int,
                    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>
        &p = *_cs;
    const unsigned int &k = p.first;
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &_x =
        p.second;
    return k;
  } else {
    return 0u;
  }
}
