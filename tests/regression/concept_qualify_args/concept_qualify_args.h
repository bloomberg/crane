#ifndef INCLUDED_CONCEPT_QUALIFY_ARGS
#define INCLUDED_CONCEPT_QUALIFY_ARGS

#include <any>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename M>
concept HasElements = requires {
  typename M::t;
  requires(
      requires {
        { M::elements } -> std::convertible_to<List<typename M::t>>;
      } ||
      requires {
        { M::elements() } -> std::convertible_to<List<typename M::t>>;
      });
  { M::head_or(std::declval<typename M::t>()) } -> std::same_as<typename M::t>;
};

struct ConceptQualifyArgs {
  template <HasElements E> struct UseElements {
    constexpr static typename E::t first_or_default(typename E::t _x0) {
      return E::head_or(_x0);
    }
  };

  struct NatElems {
    using t = uint64_t;
    static inline const List<uint64_t> elements = List<uint64_t>::cons(
        UINT64_C(1), List<uint64_t>::cons(
                         UINT64_C(2), List<uint64_t>::cons(
                                          UINT64_C(3), List<uint64_t>::nil())));
    static uint64_t head_or(uint64_t d);
  };

  using UseNatElems = UseElements<NatElems>;
  static inline const uint64_t test =
      UseNatElems::first_or_default(UINT64_C(0));
};

#endif // INCLUDED_CONCEPT_QUALIFY_ARGS
