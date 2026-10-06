#ifndef INCLUDED_REUSE_TWO_CHILDREN
#define INCLUDED_REUSE_TWO_CHILDREN

#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "field.h"
#include "obj.h"
#include "rc.h"
#include "small_vector.h"

struct Nat {};

struct ReuseTwoChildren {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::rc<tree<A>> a0;
      uint64_t a1;
      crane::field<A> a2;
      crane::rc<tree<A>> a3;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<CraneU>::Leaf>(
                    _other.v())) {
              return Leaf{};
            } else {
              const auto &[a0, a1, a2, a3] =
                  std::get<typename tree<CraneU>::Node>(_other.v());
              return Node{
                  (a0 ? crane::make_rc<tree<A>>(crane_convert<tree<A>>(*a0))
                      : nullptr),
                  a1,
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(crane::unbox(a2));
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a3 ? crane::make_rc<tree<A>>(crane_convert<tree<A>>(*a3))
                      : nullptr)};
            }
          }()) {}

    static tree<A> leaf() { return tree<A>(Leaf{}); }

    static tree<A> node(tree<A> a0, uint64_t a1, A a2, tree<A> a3) {
      return tree<A>(Node{crane::make_rc<tree<A>>(std::move(a0)), a1,
                          crane::field<A>(std::move(a2)),
                          crane::make_rc<tree<A>>(std::move(a3))});
    }

    static tree<A> node_crane_reuse(crane::rc<tree<A>> _tok, tree<A> a0,
                                    uint64_t a1, A a2, tree<A> a3) {
      return tree<A>(
          Node{crane::make_rc_reusing<tree<A>>(std::move(_tok), std::move(a0)),
               a1, crane::field<A>(std::move(a2)),
               crane::make_rc<tree<A>>(std::move(a3))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<crane::rc<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            _stack.push_back(std::move(_alt->a3));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
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

  template <typename T1, typename T2, typename F1>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0, tree_rect<T1, T2>(f, f0, *a0), a1, crane::unbox(a2), *a3,
                tree_rect<T1, T2>(f, f0, *a3));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t) {
    return tree_rect<T1, T2>(std::move(f), f0, t);
  }

  template <typename T1>
  static tree<T1> insert(uint64_t k, const T1 &v, tree<T1> t) {
    if (t.v().index() == 1) {
      if (std::get<typename tree<T1>::Node>(t.v_mut()).a0.use_count() == 1) {
        tree<T1> l =
            std::move(*std::get<typename tree<T1>::Node>(t.v_mut()).a0);
        uint64_t k_ =
            std::move(std::get<typename tree<T1>::Node>(t.v_mut()).a1);
        T1 v_ = crane::unbox(std::get<typename tree<T1>::Node>(t.v_mut()).a2);
        tree<T1> r = *std::get<typename tree<T1>::Node>(t.v_mut()).a3;
        if (k < k_) {
          return tree<T1>::node_crane_reuse(
              std::move(std::get<typename tree<T1>::Node>(t.v_mut()).a0),
              insert<T1>(k, v, std::move(l)), k_, std::move(v_), std::move(r));
        } else {
          if (k_ < k) {
            return tree<T1>::node_crane_reuse(
                std::move(std::get<typename tree<T1>::Node>(t.v_mut()).a0),
                std::move(l), k_, std::move(v_),
                insert<T1>(k, v, std::move(r)));
          } else {
            return tree<T1>::node_crane_reuse(
                std::move(std::get<typename tree<T1>::Node>(t.v_mut()).a0),
                std::move(l), k, v, std::move(r));
          }
        }
      } else {
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v_mut())) {
          return tree<T1>::node(tree<T1>::leaf(), k, v, tree<T1>::leaf());
        } else {
          auto &[a0, a1, a2, a3] = std::get<typename tree<T1>::Node>(t.v_mut());
          if (k < a1) {
            return tree<T1>::node(insert<T1>(k, v, *a0), std::move(a1),
                                  crane::unbox(a2), *a3);
          } else {
            if (a1 < k) {
              return tree<T1>::node(*a0, std::move(a1), crane::unbox(a2),
                                    insert<T1>(k, v, *a3));
            } else {
              return tree<T1>::node(*a0, k, v, *a3);
            }
          }
        }
      }
    } else {
      if (std::holds_alternative<typename tree<T1>::Leaf>(t.v_mut())) {
        return tree<T1>::node(tree<T1>::leaf(), k, v, tree<T1>::leaf());
      } else {
        auto &[a0, a1, a2, a3] = std::get<typename tree<T1>::Node>(t.v_mut());
        if (k < a1) {
          return tree<T1>::node(insert<T1>(k, v, *a0), std::move(a1),
                                crane::unbox(a2), *a3);
        } else {
          if (a1 < k) {
            return tree<T1>::node(*a0, std::move(a1), crane::unbox(a2),
                                  insert<T1>(k, v, *a3));
          } else {
            return tree<T1>::node(*a0, k, v, *a3);
          }
        }
      }
    }
  }

  template <typename T1>
  static std::optional<T1> find(uint64_t k, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename tree<T1>::Node>(t.v());
      if (k < a1) {
        return find<T1>(k, *a0);
      } else {
        if (a1 < k) {
          return find<T1>(k, *a3);
        } else {
          return std::make_optional<T1>(crane::unbox(a2));
        }
      }
    }
  }

  template <typename T1> static uint64_t size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1, a2, a3] = std::get<typename tree<T1>::Node>(t.v());
      return ((UINT64_C(1) + size<T1>(*a0)) + size<T1>(*a3));
    }
  }

  static inline const tree<uint64_t> t0 = insert<uint64_t>(
      UINT64_C(5), UINT64_C(50),
      insert<uint64_t>(
          UINT64_C(3), UINT64_C(30),
          insert<uint64_t>(
              UINT64_C(8), UINT64_C(80),
              insert<uint64_t>(UINT64_C(1), UINT64_C(10),
                               insert<uint64_t>(UINT64_C(4), UINT64_C(40),
                                                tree<uint64_t>::leaf())))));
  static inline const tree<uint64_t> t1 =
      insert<uint64_t>(UINT64_C(3), UINT64_C(33),
                       insert<uint64_t>(UINT64_C(8), UINT64_C(88), t0));
  static inline const uint64_t result = []() -> uint64_t {
    auto _cs = find<uint64_t>(UINT64_C(3), t1);
    if (_cs.has_value()) {
      const uint64_t &a = *_cs;
      auto _cs1 = find<uint64_t>(UINT64_C(8), t1);
      if (_cs1.has_value()) {
        const uint64_t &b = *_cs1;
        auto _cs2 = find<uint64_t>(UINT64_C(5), t1);
        if (_cs2.has_value()) {
          const uint64_t &c = *_cs2;
          return (((a + b) + c) + size<uint64_t>(t1));
        } else {
          return UINT64_C(0);
        }
      } else {
        return UINT64_C(0);
      }
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_REUSE_TWO_CHILDREN
