#ifndef INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT
#define INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct natPtr;
struct natProv;
struct natState;
struct natMMP;
template <typename
I>concept PtrC = requires {
  typename I::ptr;
} && (requires {
  { I::nullp() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::nullp } -> std::convertible_to<typename I::ptr>;
});
template <typename
I>concept ProvC = requires {
  typename I::provenance;
} && (requires {
  { I::noprov() } -> std::convertible_to<typename I::provenance>;
} || requires {
  { I::noprov } -> std::convertible_to<typename I::provenance>;
});
template <typename
I>concept StateC = requires {
  typename I::state;
} && (requires {
  { I::init() } -> std::convertible_to<typename I::state>;
} || requires {
  { I::init } -> std::convertible_to<typename I::state>;
});
template <typename I>
concept MMP = requires {
  typename I::PTR;
  typename I::PROV;
  typename I::mm_state;
  { I::mret(std::declval<std::any>()) } -> std::convertible_to<std::any>;
  {
    I::mbind(std::declval<std::any>(),
             std::declval<std::function<std::any(std::any)>>())
  } -> std::convertible_to<std::any>;
  { I::get_state() } -> std::convertible_to<std::any>;
  {
    I::mk_prov(std::declval<typename I::PTR::ptr>())
  } -> std::convertible_to<typename I::PROV::provenance>;
  {
    I::fresh_ptr(std::declval<typename I::mm_state::state>())
  } -> std::convertible_to<typename I::PTR::ptr>;
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using ptr = std::any;
using provenance = std::any;
using state = std::any;
template <typename x = void> using memM = std::any;

template <MMP _tcI0, typename T1> memM<T1> mret(const T1 &x) {
  return std::any_cast<memM<T1>>(_tcI0::mret(x));
}

template <MMP _tcI0, typename T1 = void, typename T2 = void, typename F1>
memM<T2> mbind(memM<std::any> x, F1 &&x0) {
  return std::any_cast<memM<T2>>(
      _tcI0::mbind(std::move(x), crane_erase_fn(x0)));
}

template <MMP _tcI0> memM<typename _tcI0::PROV::provenance> allocate() {
  return mbind<_tcI0, typename _tcI0::mm_state::state,
               typename _tcI0::PROV::provenance>(
      std::any_cast<MMP>(_tcI0::get_state()),
      [=](const typename _tcI0::mm_state::state &s) mutable {
        return mret<_tcI0, typename _tcI0::PROV::provenance>(
            std::any_cast<MMP>(_tcI0::mk_prov(_tcI0::fresh_ptr(s))));
      });
}

struct natPtr {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(PtrC<natPtr>);

struct natProv {
  using provenance = Nat;

  static Nat noprov() { return Nat::o(); }
};

static_assert(ProvC<natProv>);

struct natState {
  using state = Nat;

  static Nat init() { return Nat::o(); }
};

static_assert(StateC<natState>);

struct natMMP {
  using PTR = natPtr;
  using PROV = natProv;
  using mm_state = natState;
  using ptr = typename PTR::ptr;
  using provenance = typename PROV::provenance;
  using state = typename mm_state::state;

  static std::any mret(std::any a) { return a; }

  static std::any mbind(std::any m, std::function<std::any(std::any)> k) {
    return k(m);
  }

  static std::any get_state() {
    return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  }

  static provenance mk_prov(ptr p) {
    return Nat::s(std::any_cast<Nat>(std::move(p)));
  }

  static ptr fresh_ptr(state s) { return s; }
};

static_assert(MMP<natMMP>);

struct HkClassFieldResultCastToConcept {
  static inline const Nat run = std::any_cast<Nat>(allocate<natMMP>());
};

#endif // INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT
