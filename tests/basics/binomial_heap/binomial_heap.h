#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct BinomialHeap {
  using key = uint64_t;

  struct tree {
    // TYPES
    struct Node {
      key a0;
      std::shared_ptr<tree> a1;
      std::shared_ptr<tree> a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Leaf _v) : v_(_v) {}

    static tree node(key a0, tree a1, tree a2) {
      return tree(Node{std::move(a0), std::make_shared<tree>(std::move(a1)),
                       std::make_shared<tree>(std::move(a2))});
    }

    static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    ~tree() {
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
  static T1 tree_rect(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rect<T1>(f, f0, *a1), *a2,
               tree_rect<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
  static T1 tree_rec(F0 &&f, T1 f0, const tree &t) {
    return tree_rect<T1>(f, std::move(f0), t);
  }

  using priqueue = List<tree>;
  static inline const priqueue empty = List<tree>::nil();
  static tree smash(const tree &t, const tree &u);
  static List<tree> carry(const List<tree> &q, const tree &t);
  static priqueue insert(uint64_t x, const List<tree> &q);
  static priqueue join(const List<tree> &p, const List<tree> &q, const tree &c);

  static priqueue unzip(const tree &t, crane::fn<List<tree>(List<tree>)> cont) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a1_value = *a1;
      const tree &a2_value = *a2;
      crane::fn<List<tree>(priqueue)> f = [=,
                                           cont = std::move(cont)](priqueue q) {
        return List<tree>::cons(tree::node(a0, a1_value, tree::leaf()),
                                cont(q));
      };
      return unzip(a2_value, std::move(f));
    } else {
      return cont(List<tree>::nil());
    }
  }

  static priqueue heap_delete_max(const tree &t);
  static key find_max_helper(uint64_t current, const List<tree> &q);
  static std::optional<key> find_max(const List<tree> &q);
  static std::pair<priqueue, priqueue> delete_max_aux(uint64_t m,
                                                      const List<tree> &p);
  static std::optional<std::pair<key, priqueue>>
  delete_max(const List<tree> &q);
  static priqueue merge(const List<tree> &p, const List<tree> &q);
  static priqueue insert_list(const List<uint64_t> &l, List<tree> q);
  static List<uint64_t> make_list(uint64_t n, const List<uint64_t> &l);
  static key help(const List<tree> &c);
  static inline const key example1 = help(merge(
      insert(UINT64_C(5),
             insert(UINT64_C(3), insert(UINT64_C(7), List<tree>::nil()))),
      insert(UINT64_C(3),
             insert(UINT64_C(6), insert(UINT64_C(9), List<tree>::nil())))));
  static inline const key example2 =
      help(merge(insert_list(make_list(UINT64_C(10), List<uint64_t>::nil()),
                             List<tree>::nil()),
                 insert_list(make_list(UINT64_C(11), List<uint64_t>::nil()),
                             List<tree>::nil())));
};

#endif // INCLUDED_BINOMIAL_HEAP
