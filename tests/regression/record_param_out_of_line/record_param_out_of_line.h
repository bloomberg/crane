#ifndef INCLUDED_RECORD_PARAM_OUT_OF_LINE
#define INCLUDED_RECORD_PARAM_OUT_OF_LINE

#include <atomic>
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

struct RecordParamOutOfLine {
  struct Bag {
    Nat size;
    bool full;
    enum class Kind { SMALL, LARGE };

    template <typename T1> static T1 kind_rect(T1 f, T1 f0, Kind k) {
      switch (k) {
      case Kind::SMALL: {
        return f;
      }
      case Kind::LARGE: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 kind_rec(T1 f, T1 f0, Kind k) {
      return kind_rect(std::move(f), std::move(f0), k);
    }

    static Kind classify(const Bag &b);
  };

  static inline const Bag::Kind large =
      Bag::classify(Bag{Nat::s(Nat::s(Nat::o())), true});
};

#endif // INCLUDED_RECORD_PARAM_OUT_OF_LINE
