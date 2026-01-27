#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Comparison {
  struct comparison {
  public:
    struct Eq {};
    struct Lt {};
    struct Gt {};
    using variant_t = std::variant<Eq, Lt, Gt>;

  private:
    variant_t v_;
    explicit comparison(Eq x) : v_(std::move(x)) {}
    explicit comparison(Lt x) : v_(std::move(x)) {}
    explicit comparison(Gt x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Comparison::comparison> Eq_() {
        return std::shared_ptr<Comparison::comparison>(
            new Comparison::comparison(Eq{}));
      }
      static std::shared_ptr<Comparison::comparison> Lt_() {
        return std::shared_ptr<Comparison::comparison>(
            new Comparison::comparison(Lt{}));
      }
      static std::shared_ptr<Comparison::comparison> Gt_() {
        return std::shared_ptr<Comparison::comparison>(
            new Comparison::comparison(Gt{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

std::shared_ptr<Comparison::comparison> compare(const unsigned int n,
                                                const unsigned int m);

template <typename M>
concept BaseType = requires { typename M::t; };

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<std::shared_ptr<Comparison::comparison>>;
};

template <typename M>
concept Map = requires {
  typename M::key;
  typename M::value;
  typename M::t;
  requires std::same_as<std::remove_cvref_t<decltype(M::empty)>, typename M::t>;
  {
    M::add(std::declval<typename M::key>(), std::declval<typename M::value>(),
           std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
  {
    M::find(std::declval<typename M::key>(), std::declval<typename M::t>())
  } -> std::same_as<std::optional<typename M::value>>;
};

template <OrderedType K, BaseType V> struct MakeMap {
  using key = typename K::t;

  using value = typename V::t;

  struct tree {
  public:
    struct Empty {};
    struct Node {
      std::shared_ptr<tree> _a0;
      key _a1;
      value _a2;
      std::shared_ptr<tree> _a3;
    };
    using variant_t = std::variant<Empty, Node>;

  private:
    variant_t v_;
    explicit tree(Empty x) : v_(std::move(x)) {}
    explicit tree(Node x) : v_(std::move(x)) {}

  public:
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
    };
    const variant_t &v() const { return v_; }
  };

  using t = std::shared_ptr<tree>;

  static inline std::shared_ptr<tree> empty = tree::ctor::Empty_();

  static t add(const typename K::t k, const typename V::t v,
               const std::shared_ptr<tree> &m) {
    return std::visit(
        Overloaded{
            [&](const typename tree::Empty _args) -> std::shared_ptr<tree> {
              return tree::ctor::Node_(tree::ctor::Empty_(), k, v,
                                       tree::ctor::Empty_());
            },
            [&](const typename tree::Node _args) -> std::shared_ptr<tree> {
              std::shared_ptr<tree> l = _args._a0;
              typename K::t k_ = _args._a1;
              typename V::t v_ = _args._a2;
              std::shared_ptr<tree> r = _args._a3;
              return std::visit(
                  Overloaded{
                      [&](const typename Comparison::comparison::Eq _args)
                          -> std::shared_ptr<tree> {
                        return tree::ctor::Node_(l, k, v, r);
                      },
                      [&](const typename Comparison::comparison::Lt _args)
                          -> std::shared_ptr<tree> {
                        return tree::ctor::Node_(add(k, v, l), k_, v_, r);
                      },
                      [&](const typename Comparison::comparison::Gt _args)
                          -> std::shared_ptr<tree> {
                        return tree::ctor::Node_(l, k_, v_, add(k, v, r));
                      }},
                  K::compare(k, k_)->v());
            }},
        m->v());
  }

  static std::optional<value> find(const typename K::t k,
                                   const std::shared_ptr<tree> &m) {
    return std::visit(
        Overloaded{
            [&](const typename tree::Empty _args)
                -> std::optional<typename V::t> { return std::nullopt; },
            [&](const typename tree::Node _args)
                -> std::optional<typename V::t> {
              std::shared_ptr<tree> l = _args._a0;
              typename K::t k_ = _args._a1;
              typename V::t v_ = _args._a2;
              std::shared_ptr<tree> r = _args._a3;
              return std::visit(
                  Overloaded{
                      [&](const typename Comparison::comparison::Eq _args)
                          -> std::optional<typename V::t> {
                        return std::make_optional<typename V::t>(v_);
                      },
                      [&](const typename Comparison::comparison::Lt _args)
                          -> std::optional<typename V::t> {
                        return find(k, l);
                      },
                      [&](const typename Comparison::comparison::Gt _args)
                          -> std::optional<typename V::t> {
                        return find(k, r);
                      }},
                  K::compare(k, k_)->v());
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

  static std::shared_ptr<Comparison::comparison> compare(const unsigned int,
                                                         const unsigned int);
};
static_assert(OrderedType<NatOrdered>);

using NatMap = MakeMap<NatOrdered, NatBase>;
static_assert(Map<NatMap>);

const NatMap::t mymap = NatMap::add(
    (0 + 1), ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
    NatMap::add(
        ((0 + 1) + 1),
        ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1),
        NatMap::add(
            (((0 + 1) + 1) + 1),
            ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1),
            NatMap::empty)));
