#ifndef INCLUDED_ITREE_NESTED_BIND_INSTANCE
#define INCLUDED_ITREE_NESTED_BIND_INSTANCE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Nat;

struct ItreeNestedBindInstance {
  static std::shared_ptr<ITree<Nat>> use(const Nat &n);
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

template <typename T1 = void>
std::shared_ptr<ITree<Nat>> g(const std::shared_ptr<ITree<Nat>> &x) {
  return itree_bind(x, [=](const Nat &a) {
    return Monad_itree<crane::obj>::template bind<Nat, Nat>(x, [=](Nat b) {
      return Monad_itree<crane::obj>::template ret<Nat>(a.add(b));
    });
  });
}

#endif // INCLUDED_ITREE_NESTED_BIND_INSTANCE
