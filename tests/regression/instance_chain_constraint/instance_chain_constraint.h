#ifndef INCLUDED_INSTANCE_CHAIN_CONSTRAINT
#define INCLUDED_INSTANCE_CHAIN_CONSTRAINT

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
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

  bool leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

  Nat sub(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return *_loop_self;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return *_loop_self;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

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

template <typename
I>concept Provenance = requires {
    typename I::prov;
  } && (requires {
    { I::wildcard() } -> std::convertible_to<typename I::prov>;
  } || requires {
    { I::wildcard } -> std::convertible_to<typename I::prov>;
  });
template <typename
I>concept Pointer = requires {
    typename I::ptr;
  } && (requires {
    { I::null() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::null } -> std::convertible_to<typename I::ptr>;
  });
template <typename I, typename ptr>
concept PI = requires {
  { I::ptr_to_int(std::declval<ptr>()) } -> std::convertible_to<Nat>;
};
template <typename I, typename ptr>
concept Overlaps = requires {
  {
    I::overlaps(std::declval<ptr>(), std::declval<Nat>(), std::declval<ptr>(),
                std::declval<Nat>())
  } -> std::convertible_to<bool>;
};

struct InstanceChainConstraint {
  using prov = crane::obj;
  using ptr = crane::obj;

  template <Provenance _tcI0, Pointer _tcI1, typename _tcI2>
    requires PI<_tcI2, typename _tcI1::ptr>
  struct overlaps_ptoi {
    using prov = typename _tcI0::prov;
    using ptr = typename _tcI1::ptr;

    static bool overlaps(typename _tcI1::ptr a1, Nat sz1,
                         typename _tcI1::ptr a2, Nat sz2) {
      Nat s1 = _tcI2::ptr_to_int(std::move(a1));
      Nat s2 = _tcI2::ptr_to_int(std::move(a2));
      return (s1.leb(s2.add(sz2).sub(Nat::s(Nat::o()))) &&
              s2.leb(s1.add(sz1).sub(Nat::s(Nat::o()))));
    }
  };

  struct provNat {
    using prov = Nat;

    static Nat wildcard() { return Nat::o(); }
  };

  static_assert(Provenance<provNat>);

  struct ptrNat {
    using ptr = Nat;

    static Nat null() { return Nat::o(); }
  };

  static_assert(Pointer<ptrNat>);

  struct piNat {
    static Nat ptr_to_int(typename ptrNat::ptr p) { return p; }
  };

  static_assert(PI<piNat, typename ptrNat::ptr>);
  static bool no_overlap(const Nat &a1, const Nat &sz1, const Nat &a2,
                         const Nat &sz2);

  static inline const bool is_ok =
      (no_overlap(Nat::o(), Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                  Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))) &&
       !(no_overlap(Nat::o(), Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                    Nat::s(Nat::s(Nat::o())),
                    Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
};

#endif // INCLUDED_INSTANCE_CHAIN_CONSTRAINT
