#ifndef INCLUDED_ENUM_AFTER_USE
#define INCLUDED_ENUM_AFTER_USE

#include "crane_fn.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

enum class Comparison;

struct Nat {
  struct nat {
    // TYPES
    struct O {};

    struct S {
      std::shared_ptr<Nat::nat> a0;
    };

    using variant_t = std::variant<O, S>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nat() {}

    explicit nat(O _v) : v_(_v) {}

    explicit nat(S _v) : v_(std::move(_v)) {}

    static Nat::nat o() { return Nat::nat(O{}); }

    static Nat::nat s(Nat::nat a0) {
      return Nat::nat(S{std::make_shared<Nat::nat>(std::move(a0))});
    }

    // MANIPULATORS
    ~nat() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat::nat> {
        if (auto *_alt = std::get_if<S>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<Nat::nat> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    nat(const nat &) = default;
    nat &operator=(const nat &) = default;
    nat(nat &&) noexcept = default;
    nat &operator=(nat &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat::nat add(Nat::nat m) const {
      std::shared_ptr<Nat::nat> _head{};
      std::shared_ptr<Nat::nat> *_write = &_head;
      const Nat::nat *_loop_self = this;
      Nat::nat _loop_m = std::move(m);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename Nat::nat::O>(_sv.v())) {
          *_write = std::make_shared<Nat::nat>(std::move(_loop_m));
          break;
        } else {
          const auto &[a0] = std::get<typename Nat::nat::S>(_sv.v());
          auto _cell =
              std::make_shared<Nat::nat>(typename Nat::nat::S(nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename Nat::nat::S>((*_write)->v_mut()).a0;
          _loop_self = crane_raw(a0);
          continue;
        }
      }
      return std::move(*_head);
    }
  };

  static Comparison compare(const Nat::nat &n, const Nat::nat &m);
};
enum class Comparison { EQ, LT, GT };

/// comparison is emitted as a namespace-scope enum class *after* the struct
/// whose member functions mention it, so the member declarations refer to an
/// undeclared type.
struct EnumAfterUse {
  static Comparison c(const Nat::nat &x0_, const Nat::nat &x1_);
  static Nat::nat tonat(Comparison x);
  static inline const Nat::nat ex =
      tonat(c(Nat::nat::s(Nat::nat::o()),
              Nat::nat::s(Nat::nat::s(Nat::nat::o()))))
          .add(tonat(c(Nat::nat::s(Nat::nat::s(Nat::nat::o())),
                       Nat::nat::s(Nat::nat::o()))))
          .add(
              tonat(c(Nat::nat::s(Nat::nat::o()), Nat::nat::s(Nat::nat::o()))));
};

#endif // INCLUDED_ENUM_AFTER_USE
