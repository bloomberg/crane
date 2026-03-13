#ifndef INCLUDED_MODULE
#define INCLUDED_MODULE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct Nat {
  __attribute__((pure)) static Comparison compare(const unsigned int n,
                                                  const unsigned int m);
};

template <typename M>
concept BaseType = requires { typename M::t; };
template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Comparison>;
};
template <typename M>
concept Map = requires {
  typename M::key;
  typename M::value;
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
  {
    M::add(std::declval<typename M::key>(), std::declval<typename M::value>(),
           std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::find(std::declval<typename M::key>(), std::declval<typename M::t>())
  } -> std::same_as<std::optional<typename M::value>>;
};

/// Functor that creates a Map from an OrderedType for keys and
/// a BaseType for values, using a binary search tree internally.
template <OrderedType K, BaseType V> struct MakeMap {
  using key = typename K::t;
  using value = typename V::t;

  struct tree {
    // TYPES
    struct Empty {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      key d_a1;
      value d_a2;
      std::shared_ptr<tree> d_a3;
    };

    using variant_t = std::variant<Empty, Node>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit tree(Empty _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree> Empty_() {
        return std::shared_ptr<tree>(new tree(Empty{}));
      }

      static std::shared_ptr<tree> Node_(const std::shared_ptr<tree> &a0,
                                         key a1, value a2,
                                         const std::shared_ptr<tree> &a3) {
        return std::shared_ptr<tree>(new tree(Node{a0, a1, a2, a3}));
      }

      static std::unique_ptr<tree> Empty_uptr() {
        return std::unique_ptr<tree>(new tree(Empty{}));
      }

      static std::unique_ptr<tree> Node_uptr(const std::shared_ptr<tree> &a0,
                                             key a1, value a2,
                                             const std::shared_ptr<tree> &a3) {
        return std::unique_ptr<tree>(new tree(Node{a0, a1, a2, a3}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  using t = std::shared_ptr<tree>;

  static const std::shared_ptr<tree> &empty() {
    static const std::shared_ptr<tree> v = tree::ctor::Empty_();
    return v;
  }

  __attribute__((pure)) static t add(const typename K::t k,
                                     const typename V::t v,
                                     const std::shared_ptr<tree> &m) {
    return std::visit(
        Overloaded{
            [&](const typename tree::Empty _args) -> std::shared_ptr<tree> {
              return tree::ctor::Node_(tree::ctor::Empty_(), k, v,
                                       tree::ctor::Empty_());
            },
            [&](const typename tree::Node _args) -> std::shared_ptr<tree> {
              std::shared_ptr<tree> l = _args.d_a0;
              typename K::t k_ = _args.d_a1;
              typename V::t v_ = _args.d_a2;
              std::shared_ptr<tree> r = _args.d_a3;
              return [&](void) {
                switch (K::compare(k, k_)) {
                case Comparison::e_EQ: {
                  return tree::ctor::Node_(std::move(l), k, v, std::move(r));
                }
                case Comparison::e_LT: {
                  return tree::ctor::Node_(add(k, v, std::move(l)), k_, v_,
                                           std::move(r));
                }
                case Comparison::e_GT: {
                  return tree::ctor::Node_(std::move(l), k_, v_,
                                           add(k, v, std::move(r)));
                }
                }
              }();
            }},
        m->v());
  }

  __attribute__((pure)) static std::optional<value>
  find(const typename K::t k, const std::shared_ptr<tree> &m) {
    return std::visit(
        Overloaded{[](const typename tree::Empty _args)
                       -> std::optional<typename V::t> { return std::nullopt; },
                   [&](const typename tree::Node _args)
                       -> std::optional<typename V::t> {
                     std::shared_ptr<tree> l = _args.d_a0;
                     typename K::t k_ = _args.d_a1;
                     typename V::t v_ = _args.d_a2;
                     std::shared_ptr<tree> r = _args.d_a3;
                     return [&](void) {
                       switch (K::compare(k, k_)) {
                       case Comparison::e_EQ: {
                         return std::make_optional<typename V::t>(v_);
                       }
                       case Comparison::e_LT: {
                         return find(k, std::move(l));
                       }
                       case Comparison::e_GT: {
                         return find(k, std::move(r));
                       }
                       }
                     }();
                   }},
        m->v());
  }
};

struct NatBase {
  using t = unsigned int;
};

static_assert(BaseType<NatBase>);

struct NatOrdered {
  using t = unsigned int;
  __attribute__((pure)) static Comparison compare(const unsigned int _x0,
                                                  const unsigned int _x1);
};

static_assert(OrderedType<NatOrdered>);
using NatMap = MakeMap<NatOrdered, NatBase>;
static_assert(Map<NatMap>);
const NatMap::t mymap = NatMap::add(
    1u, 10u, NatMap::add(2u, 20u, NatMap::add(3u, 30u, NatMap::empty())));

#endif // INCLUDED_MODULE
