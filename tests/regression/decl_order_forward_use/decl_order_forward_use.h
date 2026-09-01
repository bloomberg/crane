#ifndef INCLUDED_DECL_ORDER_FORWARD_USE
#define INCLUDED_DECL_ORDER_FORWARD_USE

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

template <typename A, typename B> struct Prod;

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }

  A fst() const {
    auto &[a0, a1] = *this;
    return a0;
  }
};

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
      crane::small_vector<std::shared_ptr<Nat::nat>> _stack = {};
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

    nat(const nat &) = default;
    nat &operator=(const nat &) = default;
    nat(nat &&) noexcept = default;
    nat &operator=(nat &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat::nat div(Nat::nat y) const {
      if (std::holds_alternative<typename Nat::nat::O>(y.v_mut())) {
        return y;
      } else {
        auto &[a0] = std::get<typename Nat::nat::S>(y.v_mut());
        return Nat::divmod(*this, *a0, Nat::nat::o(), *a0).fst();
      }
    }
  };

  static Prod<Nat::nat, Nat::nat> divmod(const Nat::nat &x, const Nat::nat &y,
                                         Nat::nat q, Nat::nat u);
};

struct DeclOrderForwardUse {
  static Nat::nat d(const Nat::nat &_x0, const Nat::nat &_x1);
  static inline const Nat::nat test =
      d(Nat::nat::s(Nat::nat::s(Nat::nat::s(Nat::nat::s(
            Nat::nat::s(Nat::nat::s(Nat::nat::s(Nat::nat::o()))))))),
        Nat::nat::s(Nat::nat::s(Nat::nat::o())));
};

#endif // INCLUDED_DECL_ORDER_FORWARD_USE
