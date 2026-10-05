#ifndef INCLUDED_PARTIAL_APPLY
#define INCLUDED_PARTIAL_APPLY

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct PartialApply {
  static List<uint64_t> inc_all(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>> tag_all(const List<uint64_t> &l);
  static List<std::optional<uint64_t>> wrap_all(const List<uint64_t> &l);
  static List<crane::fn<List<uint64_t>(List<uint64_t>)>>
  prepend_each(const List<uint64_t> &l);

  template <typename A> struct tagged {
    // DATA
    uint64_t a0;
    A a1;

    // ACCESSORS
    tagged<A> clone() const { return {a0, a1}; }

    template <typename CraneU>
      requires crane_convertible<CraneU, const A &>
    operator tagged<CraneU>() const {
      return {a0, crane_convert<CraneU>(a1)};
    }

    // CREATORS
    static tagged<A> tag(uint64_t a0, A a1) { return {a0, std::move(a1)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const uint64_t &, const T1 &>
  static T2 tagged_rect(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const uint64_t &, const T1 &>
  static T2 tagged_rec(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  static List<tagged<bool>> tag_with(uint64_t n, const List<bool> &l);
  static List<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>>
  double_tag(const List<uint64_t> &l);
  static uint64_t sum_with_init(uint64_t init, const List<uint64_t> &l);
  static inline const List<uint64_t> test_inc = inc_all(List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil()))));
  static inline const List<std::pair<uint64_t, uint64_t>> test_tag =
      tag_all(List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const List<std::optional<uint64_t>> test_wrap =
      wrap_all(List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))));
  static inline const List<tagged<bool>> test_tag_with = tag_with(
      UINT64_C(99),
      List<bool>::cons(
          true,
          List<bool>::cons(false, List<bool>::cons(true, List<bool>::nil()))));
  static constexpr uint64_t test_sum = UINT64_C(106);
};

#endif // INCLUDED_PARTIAL_APPLY
