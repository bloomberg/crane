#ifndef INCLUDED_ROCQ_BUG_16288
#define INCLUDED_ROCQ_BUG_16288

#include "crane_fn.h"
#include "obj.h"
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

template <typename M>
concept Nop = true;

struct RocqBug16288 {
  struct Empty {};

  template <Nop N> struct M {
    template <typename elt> struct M_t_NonEmpty {
      List<elt> M_m;

      // ACCESSORS
      template <typename CraneU> operator M_t_NonEmpty<CraneU>() const {
        return {crane_convert<List<CraneU>>(M_m)};
      }
    };

    template <typename X, typename Y> struct M_t_NonEmpty_ {
      X a;
      Y b;

      // ACCESSORS
      template <typename CraneU0, typename CraneU1>
      operator M_t_NonEmpty_<CraneU0, CraneU1>() const {
        return {[&]() -> CraneU0 {
                  if constexpr (crane_convertible<CraneU0, const X &>) {
                    return crane_convert<CraneU0>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                [&]() -> CraneU1 {
                  if constexpr (crane_convertible<CraneU1, const Y &>) {
                    return crane_convert<CraneU1>(b);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
      }
    };
  };

  using M_ = M<Empty>;
};

#endif // INCLUDED_ROCQ_BUG_16288
