#ifndef INCLUDED_CONCEPT_BEFORE_STRUCT
#define INCLUDED_CONCEPT_BEFORE_STRUCT

#include "fn.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

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

struct PeanoNat {
  static Nat add(const Nat &n, Nat m);
};

/// A class whose method returns a record type.  The concept is emitted at
/// namespace scope *before* the struct that defines the record, but its body
/// names ConceptBeforeStruct::mo.
struct ConceptBeforeStruct {
  struct mo {
    Nat mz;
    crane::fn<Nat(Nat, Nat)> mop;
  };

  struct hn {
    static mo getm() { return mo{Nat::o(), PeanoNat::add}; }
  };

  static inline const Nat ex =
      hn::getm().mop(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
};

template <typename I, typename A>
concept HasM = requires {
  { I::getm() } -> std::convertible_to<ConceptBeforeStruct::mo>;
};

static_assert(HasM<ConceptBeforeStruct::hn, Nat>);

#endif // INCLUDED_CONCEPT_BEFORE_STRUCT
