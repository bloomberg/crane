#ifndef INCLUDED_LENT_ALIAS_BY_REFERENCE
#define INCLUDED_LENT_ALIAS_BY_REFERENCE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
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

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

/// A lent parameter of a value inductive is passed by const reference
/// whether its type names the inductive or an abbreviation of it
/// (Translation_support.names_value_inductive); a frame machine holds one
/// so by pointer.
struct LentAliasByReference {
  using bag = List<uint64_t>;
  template <typename a> using table = List<std::pair<uint64_t, a>>;
  /// An abbreviation of an abbreviation.
  using big_bag = bag;
  /// Read only: lent, by const reference.
  static uint64_t bag_size(const bag &x0_);
  static uint64_t big_bag_size(const big_bag &x0_);
  /// Not tail recursive: a frame machine, whose frames point at the cells of
  /// the lent bag rather than copying them.
  static uint64_t bag_sum(const List<uint64_t> &b);

  template <typename T1>
  static T1 lookup(uint64_t k, T1 d, const List<std::pair<uint64_t, T1>> &t) {
    const List<std::pair<uint64_t, T1>> *_loop_t = &t;
    while (true) {
      if (std::holds_alternative<typename List<std::pair<uint64_t, T1>>::Nil>(
              _loop_t->v())) {
        return d;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, T1>>::Cons>(
                _loop_t->v());
        const auto &[k_, v] = a0;
        if (k == k_) {
          return std::move(v);
        } else {
          _loop_t = crane_raw(a1);
        }
      }
    }
  }

  /// Two lent abbreviation-typed parameters, walked in step.
  static uint64_t dot(const List<uint64_t> &a, const List<uint64_t> &b);
  /// Kept whole: owned, by value, moved in.
  static bag push(uint64_t x, const List<uint64_t> &b);
  static inline const bag sample = List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil()))));
  static inline const table<uint64_t> names =
      List<std::pair<uint64_t, uint64_t>>::cons(
          std::make_pair(UINT64_C(1), UINT64_C(10)),
          List<std::pair<uint64_t, uint64_t>>::cons(
              std::make_pair(UINT64_C(2), UINT64_C(20)),
              List<std::pair<uint64_t, uint64_t>>::cons(
                  std::make_pair(UINT64_C(3), UINT64_C(30)),
                  List<std::pair<uint64_t, uint64_t>>::nil())));
  static inline const uint64_t test_size = bag_size(sample);
  static inline const uint64_t test_big_size =
      big_bag_size(push(UINT64_C(0), sample));
  static inline const uint64_t test_sum = bag_sum(sample);
  static inline const uint64_t test_lookup_hit =
      lookup<uint64_t>(UINT64_C(2), UINT64_C(0), names);
  static inline const uint64_t test_lookup_miss =
      lookup<uint64_t>(UINT64_C(7), UINT64_C(99), names);
  static inline const uint64_t test_dot =
      dot(sample, push(UINT64_C(5), sample));
};

#endif // INCLUDED_LENT_ALIAS_BY_REFERENCE
