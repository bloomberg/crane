#ifndef INCLUDED_ITREE_MAPPING_HIJACKS_MONAD
#define INCLUDED_ITREE_MAPPING_HIJACKS_MONAD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename X> struct Err;
struct Monad_Err;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

struct ItreeMappingHijacksMonad {
  static Err<Nat> use(const Nat &n);
};

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

template <typename X> struct Err {
  // TYPES
  struct Ok {
    X x;
  };

  struct Bad {};

  using variant_t = std::variant<Ok, Bad>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Err() {}

  explicit Err(Ok _v) : v_(std::move(_v)) {}

  explicit Err(Bad _v) : v_(_v) {}

  template <typename CraneU>
  Err(const Err<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Err<CraneU>::Ok>(_other.v())) {
            const auto &[x] = std::get<typename Err<CraneU>::Ok>(_other.v());
            return Ok{[&]() -> X {
              if constexpr (crane_convertible<X, const CraneU &>) {
                return crane_convert<X>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return Bad{};
          }
        }()) {}

  static Err<X> ok(X x) { return Err<X>(Ok{std::move(x)}); }

  static Err<X> bad() { return Err<X>(Bad{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Monad_Err {
  template <typename CraneA0> using m = Err<CraneA0>;

  template <typename CraneA0> static Err<CraneA0> ret(CraneA0 x) {
    return Err<CraneA0>::ok(std::move(x));
  }

  template <typename CraneA0, typename CraneA1>
  static Err<CraneA1> bind(Err<CraneA0> c, crane::fn<Err<CraneA1>(CraneA0)> k) {
    if (std::holds_alternative<typename Err<CraneA0>::Ok>(c.v())) {
      const auto &[x0] = std::get<typename Err<CraneA0>::Ok>(c.v());
      return k(x0);
    } else {
      return Err<CraneA1>::bad();
    }
  }
};

static_assert(Monad<Monad_Err>);
Err<Nat> twice(const Err<Nat> &x);

#endif // INCLUDED_ITREE_MAPPING_HIJACKS_MONAD
