#ifndef INCLUDED_MEMBER_ALIAS_AS_TT_ARG
#define INCLUDED_MEMBER_ALIAS_AS_TT_ARG

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Monad_option;
struct Nat;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::ret(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::bind(std::declval<typename I::template m<crane::obj>>(),
            std::declval<
                crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

struct MemberAliasAsTtArg {
  static std::optional<std::pair<Nat, Nat>> use(const Nat &o);
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
};

struct Monad_option {
  template <typename CraneA0> using m = std::optional<CraneA0>;

  static std::optional<crane::obj> ret(crane::obj x) {
    return std::make_optional<crane::obj>(crane::obj(x));
  }

  static std::optional<crane::obj>
  bind(std::optional<crane::obj> c1,
       crane::fn<std::optional<crane::obj>(crane::obj)> c2) {
    if (c1.has_value()) {
      const crane::obj &v = *c1;
      return c2(v);
    } else {
      return std::optional<crane::obj>();
    }
  }
};

static_assert(Monad<Monad_option>);
template <typename s, template <typename> class m, typename a>
using stateT = crane::fn<m<std::pair<a, s>>(s)>;

template <Monad _tcI0, typename T2>
typename _tcI0::template m<std::pair<Nat, T2>>
run(std::type_identity_t<stateT<T2, _tcI0::template m, Nat>> step, T2 x0_) {
  return crane_container_cast<typename _tcI0::template m<std::pair<Nat, T2>>>(
      step(std::move(x0_)));
}

#endif // INCLUDED_MEMBER_ALIAS_AS_TT_ARG
