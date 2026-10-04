#ifndef INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT
#define INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct natPtr;
struct natProv;
struct natState;
struct natMMP;
using ptr = crane::obj;
using provenance = crane::obj;
using state = crane::obj;
template <typename x = void> using memM = crane::obj;
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
template <typename I, typename ptr, typename provenance, typename state>
concept MMP = requires {
  typename I::PTR;
  typename I::PROV;
  typename I::mm_state;
  { I::mret(std::declval<crane::obj>()) } -> std::convertible_to<crane::obj>;
  {
    I::mbind(std::declval<crane::obj>(),
             std::declval<crane::fn<crane::obj(crane::obj)>>())
  } -> std::convertible_to<crane::obj>;
  { I::get_state() } -> std::convertible_to<crane::obj>;
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

template <typename _tcI0, typename T1>
  requires MMP<_tcI0, typename _tcI0::PTR::ptr,
               typename _tcI0::PROV::provenance,
               typename _tcI0::mm_state::state>
memM<T1> mret(const T1 &x) {
  return _tcI0::mret(x);
}

template <typename _tcI0, typename T1 = void, typename T2 = void, typename F1>
  requires MMP<_tcI0, typename _tcI0::PTR::ptr,
               typename _tcI0::PROV::provenance,
               typename _tcI0::mm_state::state>
memM<T2> mbind(memM<crane::obj> x, F1 &&x0) {
  return _tcI0::mbind(std::move(x), crane_erase_fn(x0));
}

template <typename _tcI0>
  requires MMP<_tcI0, typename _tcI0::PTR::ptr,
               typename _tcI0::PROV::provenance,
               typename _tcI0::mm_state::state>
memM<typename _tcI0::PROV::provenance> allocate() {
  return mbind<_tcI0, typename _tcI0::mm_state::state,
               typename _tcI0::PROV::provenance>(
      _tcI0::get_state(), [=](const typename _tcI0::mm_state::state &s) {
        return mret<_tcI0, typename _tcI0::PROV::provenance>(
            _tcI0::mk_prov(_tcI0::fresh_ptr(s)));
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

  static crane::obj mret(crane::obj a) { return a; }

  static crane::obj mbind(crane::obj m, crane::fn<crane::obj(crane::obj)> k) {
    return k(m);
  }

  static crane::obj get_state() {
    return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  }

  static provenance mk_prov(ptr p) {
    return Nat::s(crane::any_cast<Nat>(std::move(p)));
  }

  static ptr fresh_ptr(state s) { return s; }
};

static_assert(MMP<natMMP, ptr, provenance, state>);

struct HkClassFieldResultCastToConcept {
  static inline const Nat run = crane::any_cast<Nat>(allocate<natMMP>());
};

#endif // INCLUDED_HK_CLASS_FIELD_RESULT_CAST_TO_CONCEPT
