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
  struct Eq;
  struct Lt;
  struct Gt;
  using comparison = std::variant<Eq, Lt, Gt>;
  struct Eq {
    static std::shared_ptr<comparison> make();
  };
  struct Lt {
    static std::shared_ptr<comparison> make();
  };
  struct Gt {
    static std::shared_ptr<comparison> make();
  };
};

std::shared_ptr<typename Comparison::comparison> compare(const unsigned int n,
                                                         const unsigned int m);

template <typename M>
concept BaseType = requires { typename M::t; };

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<std::shared_ptr<typename Comparison::comparison>>;
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
  using key = K::t;

  using value = V::t;

  struct Tree {
    struct Empty;
    struct Node;
    using tree = std::variant<Empty, Node>;
    struct Empty {
      static std::shared_ptr<tree> make();
    };
    struct Node {
      std::shared_ptr<tree> _a0;
      key _a1;
      value _a2;
      std::shared_ptr<tree> _a3;
      static std::shared_ptr<tree> make(std::shared_ptr<tree> _a0, key _a1,
                                        value _a2, std::shared_ptr<tree> _a3);
    };
  };

  using t = std::shared_ptr<typename Tree::tree>;

  static inline const std::shared_ptr<typename Tree::tree> empty =
      Tree::Empty::make();

  static t add(const K::t k, const V::t v,
               const std::shared_ptr<typename Tree::tree> m);

  static std::optional<value>
  find(const K::t k, const std::shared_ptr<typename Tree::tree> m);
};

struct NatBase {
  using t = unsigned int;
};
static_assert(BaseType<NatBase>);

struct NatOrdered {
  using t = unsigned int;

  static std::shared_ptr<typename Comparison::comparison>
  compare(const unsigned int, const unsigned int);
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
