#ifndef INCLUDED_CONCEPT_QUALIFY_ARGS
#define INCLUDED_CONCEPT_QUALIFY_ARGS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
    static typename E::t first_or_default(typename E::t x0_) {
      return E::head_or(std::move(x0_));
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
