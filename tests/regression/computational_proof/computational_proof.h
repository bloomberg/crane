#ifndef INCLUDED_COMPUTATIONAL_PROOF
#define INCLUDED_COMPUTATIONAL_PROOF

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ComputationalProof {
  static bool nat_eq_dec(uint64_t n, uint64_t x);
  static bool nat_eqb_dec(uint64_t n, uint64_t m);
  static bool le_dec(uint64_t n, uint64_t m);
  static bool nat_leb_dec(uint64_t n, uint64_t m);
  static uint64_t min_dec(uint64_t n, uint64_t m);
  static uint64_t max_dec(uint64_t n, uint64_t m);
  static List<uint64_t> insert_dec(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> isort_dec(const List<uint64_t> &l);
  static inline const bool test_eq_true = nat_eqb_dec(UINT64_C(5), UINT64_C(5));
  static inline const bool test_eq_false =
      nat_eqb_dec(UINT64_C(3), UINT64_C(7));
  static inline const bool test_leb_true =
      nat_leb_dec(UINT64_C(3), UINT64_C(5));
  static inline const bool test_leb_false =
      nat_leb_dec(UINT64_C(8), UINT64_C(2));
  static inline const uint64_t test_min = min_dec(UINT64_C(4), UINT64_C(9));
  static inline const uint64_t test_max = max_dec(UINT64_C(4), UINT64_C(9));
  static inline const List<uint64_t> test_sort = isort_dec(List<uint64_t>::cons(
      UINT64_C(5),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))));
};

#endif // INCLUDED_COMPUTATIONAL_PROOF
