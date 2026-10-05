#ifndef INCLUDED_LOOPIFY_LIST_WINDOWS
#define INCLUDED_LOOPIFY_LIST_WINDOWS

#include "crane_fn.h"
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

struct LoopifyListWindows {
  static uint64_t len(const List<uint64_t> &l);
  static List<List<uint64_t>> map_cons_helper(uint64_t x,
                                              const List<List<uint64_t>> &ll);
  static List<uint64_t> drop(uint64_t m, List<uint64_t> xs);
  static std::pair<List<uint64_t>, List<uint64_t>>
  span_eq(uint64_t first, const List<uint64_t> &lst);
  static List<uint64_t> differences(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  sliding_pairs(const List<uint64_t> &l);
  static List<List<uint64_t>> inits(const List<uint64_t> &l);
  static List<List<uint64_t>> tails(const List<uint64_t> &l);
  static List<uint64_t> take(uint64_t n, const List<uint64_t> &l);
  static List<List<uint64_t>> windows_fuel(uint64_t fuel, uint64_t n,
                                           const List<uint64_t> &l);
  static List<List<uint64_t>> windows(uint64_t n, const List<uint64_t> &l);
  static List<List<uint64_t>> chunks_fuel(uint64_t fuel, uint64_t n,
                                          List<uint64_t> l);
  static List<List<uint64_t>> chunks(uint64_t n, List<uint64_t> l);
  static List<List<uint64_t>> group_fuel(uint64_t fuel,
                                         const List<uint64_t> &l);
  static List<List<uint64_t>> group(const List<uint64_t> &l);
};

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

#endif // INCLUDED_LOOPIFY_LIST_WINDOWS
