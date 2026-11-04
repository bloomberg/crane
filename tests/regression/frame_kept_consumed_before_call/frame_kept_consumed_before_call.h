#ifndef INCLUDED_FRAME_KEPT_CONSUMED_BEFORE_CALL
#define INCLUDED_FRAME_KEPT_CONSUMED_BEFORE_CALL

#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "obj.h"
#include "rc.h"
#include "small_vector.h"

template <typename A> struct List;

struct FrameKeptConsumedBeforeCall {
  static List<uint64_t> snoc(List<uint64_t> x);
  static List<List<uint64_t>> pairs(uint64_t fuel, List<List<uint64_t>> l);
  static List<List<uint64_t>> again(uint64_t fuel, List<List<uint64_t>> l);
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::rc<List<A>> l;
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
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (l ? crane::make_rc<List<A>>(crane_convert<List<A>>(*l))
                           : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  static List<A> cons_crane_reuse(crane::rc<List<A>> _tok, A a, List<A> l) {
    return List<A>(Cons{std::move(a), crane::make_rc_reusing<List<A>>(
                                          std::move(_tok), std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> crane::rc<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    crane::rc<List<A>> _cur = _next(v_mut());
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

#endif // INCLUDED_FRAME_KEPT_CONSUMED_BEFORE_CALL
