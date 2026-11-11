#ifndef INCLUDED_INDUCTIVE_LETIN_PARAMS
#define INCLUDED_INDUCTIVE_LETIN_PARAMS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
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
};

struct InductiveLetinParams {
  /// A let-in between two type parameters, used by a field.
  template <typename A, typename B> struct tri {
    // DATA
    A a0;
    B a1;
    List<A> a2;

    // ACCESSORS
    tri<A, B> clone() const { return {a0, a1, a2}; }

    template <typename CraneU0, typename CraneU1>
    operator tri<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              crane_convert<List<CraneU0>>(a2)};
    }

    // CREATORS
    static tri<A, B> tri0(A a0, B a1, List<A> a2) {
      return {std::move(a0), std::move(a1), std::move(a2)};
    }

    List<A> tri_rest() const {
      const auto &[a0, a1, a2] = *this;
      return a2;
    }

    B tri_second() const {
      const auto &[a0, a1, a2] = *this;
      return a1;
    }

    A tri_first() const {
      const auto &[a0, a1, a2] = *this;
      return a0;
    }

    template <typename T1, typename F0> T1 tri_rec(F0 &&f) const {
      return this->template tri_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &, const B &,
                                     const List<A> &>
    T1 tri_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }
  };

  static inline const tri<uint64_t, bool> sample = tri<uint64_t, bool>::tri0(
      UINT64_C(7), true,
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
  static inline const uint64_t sample_sum =
      sample.tri_rest().template fold_left<uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          sample.tri_first());

  /// A let-in after the type parameters, in a recursive inductive.
  template <typename A, typename B> struct tagged {
    // TYPES
    struct Tnil {};

    struct Tcons {
      std::pair<A, B> a0;
      std::shared_ptr<tagged<A, B>> a1;
    };

    using variant_t = std::variant<Tnil, Tcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tagged() {}

    explicit tagged(Tnil _v) : v_(_v) {}

    explicit tagged(Tcons _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    tagged(const tagged<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tagged<CraneU0, CraneU1>::Tnil>(
                    _other.v())) {
              return Tnil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename tagged<CraneU0, CraneU1>::Tcons>(
                      _other.v());
              return Tcons{std::pair<A, B>(a0),
                           (a1 ? std::make_shared<tagged<A, B>>(
                                     crane_convert<tagged<A, B>>(*a1))
                               : nullptr)};
            }
          }()) {}

    static tagged<A, B> tnil() { return tagged<A, B>(Tnil{}); }

    static tagged<A, B> tcons(std::pair<A, B> a0, tagged<A, B> a1) {
      return tagged<A, B>(
          Tcons{std::move(a0), std::make_shared<tagged<A, B>>(std::move(a1))});
    }

    // MANIPULATORS
    ~tagged() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<tagged<A, B>> {
        if (auto *_alt = std::get_if<Tcons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<tagged<A, B>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    tagged(const tagged &) = default;
    tagged &operator=(const tagged &) = default;
    tagged(tagged &&) = default;
    tagged &operator=(tagged &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    List<B> tagged_seconds() const {
      std::optional<List<B>> _root{};
      std::shared_ptr<List<B>> *_write = nullptr;
      const tagged<A, B> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tagged<A, B>::Tnil>(_sv.v())) {
          auto _value = List<B>::nil();
          (_write ? *(*_write = std::make_shared<List<B>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename tagged<A, B>::Tcons>(_sv.v());
          auto _cell = typename List<B>::Cons(a0.second, nullptr);
          List<B> &_node =
              (_write ? *(*_write = std::make_shared<List<B>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<B>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    List<A> tagged_firsts() const {
      std::optional<List<A>> _root{};
      std::shared_ptr<List<A>> *_write = nullptr;
      const tagged<A, B> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tagged<A, B>::Tnil>(_sv.v())) {
          auto _value = List<A>::nil();
          (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] =
              std::get<typename tagged<A, B>::Tcons>(_sv.v());
          auto _cell = typename List<A>::Cons(a0.first, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    template <typename T1, typename F1> T1 tagged_rec(T1 f, F1 &&f0) const {
      return this->template tagged_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tagged_rect(T1 f, F1 &&f0) const {
      const tagged<A, B> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tagged<A, B> *_self;
      };

      /// CraneCont_Tcons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Tcons {
        std::pair<A, B> a0;
        std::shared_ptr<tagged<A, B>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Tcons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tagged_rect: CraneEnter -> CraneCont_Tcons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tagged<A, B> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tagged<A, B>::Tnil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename tagged<A, B>::Tcons>(_sv.v());
            _stack.emplace_back(CraneCont_Tcons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Tcons>(_frame));
          std::pair<A, B> a0 = std::move(_f.a0);
          std::shared_ptr<tagged<A, B>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const tagged<uint64_t, bool> sample_tagged =
      tagged<uint64_t, bool>::tcons(
          std::make_pair(UINT64_C(1), true),
          tagged<uint64_t, bool>::tcons(std::make_pair(UINT64_C(2), false),
                                        tagged<uint64_t, bool>::tnil()));

  /// A let-in parameter before an index the constructor binds: the field
  /// x : T reads its type through the binder of T, found by de Bruijn
  /// level past the parameter context, the let-in counted.
  struct wrap {
    // DATA
    crane::obj t;

    // ACCESSORS
    wrap clone() const { return {t}; }

    // CREATORS
    static wrap wrap0(crane::obj t) { return {std::move(t)}; }

    template <typename T1> T1 unwrap() const {
      const auto &[t] = *this;
      return crane_any_cast<T1>(t);
    }

    template <typename T1, typename T2, typename F0> T1 wrap_rec(F0 &&f) const {
      const auto &[t0] = *this;
      return crane_any_cast<T1>(crane_call_erased(f, crane_any_cast<T2>(t0)));
    }

    template <typename T1, typename T2, typename F0>
    T1 wrap_rect(F0 &&f) const {
      const auto &[t0] = *this;
      return crane_any_cast<T1>(crane_call_erased(f, crane_any_cast<T2>(t0)));
    }
  };

  static inline const wrap sample_wrap = wrap::wrap0(UINT64_C(5));
  static inline const uint64_t unwrapped =
      crane::any_cast<const uint64_t>(sample_wrap.template unwrap<uint64_t>());
};

#endif // INCLUDED_INDUCTIVE_LETIN_PARAMS
