#ifndef INCLUDED_FAMILY_CALL_RESULT_DEEP_SHAPE
#define INCLUDED_FAMILY_CALL_RESULT_DEEP_SHAPE

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

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
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

struct FamilyCallResultDeepShape {
  struct ty {
    // TYPES
    struct TNat {};

    struct TPair {
      std::shared_ptr<ty> a0;
      std::shared_ptr<ty> a1;
    };

    struct TList {
      std::shared_ptr<ty> a0;
    };

    using variant_t = std::variant<TNat, TPair, TList>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TNat _v) : v_(_v) {}

    explicit ty(TPair _v) : v_(std::move(_v)) {}

    explicit ty(TList _v) : v_(std::move(_v)) {}

    static ty tnat() { return ty(TNat{}); }

    static ty tpair(ty a0, ty a1) {
      return ty(TPair{std::make_shared<ty>(std::move(a0)),
                      std::make_shared<ty>(std::move(a1))});
    }

    static ty tlist(ty a0) {
      return ty(TList{std::make_shared<ty>(std::move(a0))});
    }

    // MANIPULATORS
    ~ty() {
      if (std::holds_alternative<TNat>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<TPair>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<TList>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ty>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TPair>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<TList>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) = default;
    ty &operator=(ty &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F2>
  static T1 ty_rect(T1 f, F1 &&f0, F2 &&f1, const ty &t) {
    if (std::holds_alternative<typename ty::TNat>(t.v())) {
      return f;
    } else if (std::holds_alternative<typename ty::TPair>(t.v())) {
      const auto &[a0, a1] = std::get<typename ty::TPair>(t.v());
      return f0(*a0, ty_rect<T1>(f, f0, f1, *a0), *a1,
                ty_rect<T1>(f, f0, f1, *a1));
    } else {
      const auto &[a0] = std::get<typename ty::TList>(t.v());
      return f1(*a0, ty_rect<T1>(std::move(f), f0, f1, *a0));
    }
  }

  template <typename T1, typename F1, typename F2>
  static T1 ty_rec(T1 f, F1 &&f0, F2 &&f1, const ty &t) {
    return ty_rect<T1>(std::move(f), f0, f1, t);
  }

  using den = crane::obj;
  static uint64_t sz(const ty &t, den n);
  static den mk(uint64_t n);
  static inline const uint64_t result =
      sz(ty::tlist(ty::tpair(ty::tnat(), ty::tnat())), mk(UINT64_C(3)));
};

#endif // INCLUDED_FAMILY_CALL_RESULT_DEEP_SHAPE
