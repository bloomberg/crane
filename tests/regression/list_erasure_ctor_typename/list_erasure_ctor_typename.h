#ifndef INCLUDED_LIST_ERASURE_CTOR_TYPENAME
#define INCLUDED_LIST_ERASURE_CTOR_TYPENAME

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct List {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<typename List::template list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const typename List::template list<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<typename List::template list<A>>(nullptr),
              [](const typename List::template list<CraneU> &_cell)
                  -> const typename List::template list<CraneU> * {
                if (std::holds_alternative<
                        typename List::template list<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename List::template list<CraneU>::Cons>(
                             _cell.v())
                      .l.get();
                } else {
                  return nullptr;
                }
              },
              [&](const typename List::template list<CraneU> &_other,
                  std::shared_ptr<typename List::template list<A>> _below)
                  -> variant_t {
                if (std::holds_alternative<
                        typename List::template list<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a, l] =
                      std::get<typename List::template list<CraneU>::Cons>(
                          _other.v());
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
                return std::make_shared<typename List::template list<A>>(
                    std::move(_alt));
              })) {}

    static typename List::template list<A> nil() {
      return typename List::template list<A>(Nil{});
    }

    static typename List::template list<A> cons(A a, List::list<A> l) {
      return typename List::template list<A>(Cons{
          std::move(a),
          std::make_shared<typename List::template list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v)
          -> std::shared_ptr<typename List::template list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<typename List::template list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1>
  static std::optional<T1> nth_error(const List::list<T1> &l, uint64_t n);
};

/// Using nth_error on a list (nat -> nat) instantiates the
/// erasure-converting List constructor, whose body names the source
/// instantiation's constructor structs.  Because list is not merged into
/// its List wrapper struct, those names are dependent and must be spelled
/// typename List::template list<_U>::Nil.
struct ListErasureCtorTypename {
  static std::optional<crane::fn<uint64_t(uint64_t)>> pick(uint64_t n);
  static constexpr uint64_t go = UINT64_C(42);
};

template <typename T1>
std::optional<T1> List::nth_error(const List::list<T1> &l, uint64_t n) {
  if (n <= 0) {
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1] = std::get<typename List::list<T1>::Cons>(l.v());
      return std::make_optional<T1>(a0);
    }
  } else {
    uint64_t n0 = n - 1;
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a00, a10] = std::get<typename List::list<T1>::Cons>(l.v());
      return List::template nth_error<T1>(*a10, n0);
    }
  }
}

#endif // INCLUDED_LIST_ERASURE_CTOR_TYPENAME
