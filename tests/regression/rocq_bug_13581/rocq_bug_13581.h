#ifndef INCLUDED_ROCQ_BUG_13581
#define INCLUDED_ROCQ_BUG_13581

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

enum class Unit;
enum class Bool0;
struct Nat;
enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct RocqBug13581 {
  template <typename T0> struct mixin_of {
    crane::fn<T0(T0)> mixin_f;

    // ACCESSORS
    template <typename CraneU> operator mixin_of<CraneU>() const {
      return {crane_convert<crane::fn<CraneU(CraneU)>>(mixin_f)};
    }
  };

  static inline const mixin_of<Nat> d =
      mixin_of<Nat>{[](Nat x0) { return x0; }};

  template <typename T0> struct R {
    crane::fn<T0(T0)> g;
    Nat x;

    // ACCESSORS
    template <typename CraneU> operator R<CraneU>() const {
      return {crane_convert<crane::fn<CraneU(CraneU)>>(g), x};
    }
  };

  template <typename T1>
  static Nat y(const Nat &, const Nat &, const R<T1> &r0) {
    return r0.x.add(r0.x);
  }

  static inline const R<Nat> r = R<Nat>{[](Nat x0) { return x0; }, Nat::o()};
  template <typename T> struct I;
  template <typename T> struct J;

  template <typename T> struct I {
    // TYPES
    struct C {};

    struct D {
      std::shared_ptr<J<T>> a0;
    };

    using variant_t = std::variant<C, D>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    I() {}

    explicit I(C _v) : v_(_v) {}

    explicit I(D _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    I(const I<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename I<CraneU>::C>(_other.v())) {
              return C{};
            } else {
              const auto &[a0] = std::get<typename I<CraneU>::D>(_other.v());
              return D{(a0 ? std::make_shared<J<T>>(crane_convert<J<T>>(*a0))
                           : nullptr)};
            }
          }()) {}

    static I<T> c() { return I<T>(C{}); }

    static I<T> d(J<T> a0) {
      return I<T>(D{std::make_shared<J<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~I() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<D>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<I<T>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<J<T>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename J<T>::E>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    I(const I &) = default;
    I &operator=(const I &) = default;
    I(I &&) = default;
    I &operator=(I &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T> struct J {
    // TYPES
    struct E {
      std::shared_ptr<I<T>> a0;
    };

    using variant_t = std::variant<E>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    J() {}

    explicit J(E _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    J(const J<CraneU> &_other)
        : v_([&]() -> variant_t {
            const auto &[a0] = std::get<typename J<CraneU>::E>(_other.v());
            return E{(a0 ? std::make_shared<I<T>>(crane_convert<I<T>>(*a0))
                         : nullptr)};
          }()) {}

    static J<T> e(I<T> a0) {
      return J<T>(E{std::make_shared<I<T>>(std::move(a0))});
    }

    // MANIPULATORS
    ~J() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<E>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<J<T>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<I<T>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename I<T>::D>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    J(const J &) = default;
    J &operator=(const J &) = default;
    J(J &&) = default;
    J &operator=(J &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F3>
  static T2 I_rect(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                   const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F3>
  static T2 I_rec(const T1 &, const T1 &, T2 f, F3 &&f0, const Nat &,
                  const I<T1> &i) {
    if (std::holds_alternative<typename I<T1>::C>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename I<T1>::D>(i.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F2>
  static T2 J_rect(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  template <typename T1, typename T2, typename F2>
  static T2 J_rec(const T1 &, const T1 &, F2 &&f, Bool0, const J<T1> &j) {
    const auto &[a0] = std::get<typename J<T1>::E>(j.v());
    return f(*a0);
  }

  static inline const I<Nat> c = I<Nat>::d(J<Nat>::e(I<Nat>::c()));
};

#endif // INCLUDED_ROCQ_BUG_13581
