#ifndef INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS
#define INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <stdexcept>
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

struct Bag {
  template <typename A> struct bag {
    // TYPES
    struct Empty {};

    struct Add {
      A a0;
      std::shared_ptr<typename Bag::template bag<A>> a1;
    };

    using variant_t = std::variant<Empty, Add>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bag() {}

    explicit bag(Empty _v) : v_(_v) {}

    explicit bag(Add _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    bag(const typename Bag::template bag<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<
                    typename Bag::template bag<CraneU>::Empty>(_other.v())) {
              return Empty{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename Bag::template bag<CraneU>::Add>(_other.v());
              return Add{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<typename Bag::template bag<A>>(
                            crane_convert<typename Bag::template bag<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static typename Bag::template bag<A> empty() {
      return typename Bag::template bag<A>(Empty{});
    }

    static typename Bag::template bag<A> add(A a0, Bag::bag<A> a1) {
      return typename Bag::template bag<A>(
          Add{std::move(a0),
              std::make_shared<typename Bag::template bag<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~bag() {
      auto _next =
          [&](variant_t &_v) -> std::shared_ptr<typename Bag::template bag<A>> {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<typename Bag::template bag<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    bag(const bag &) = default;
    bag &operator=(const bag &) = default;
    bag(bag &&) = default;
    bag &operator=(bag &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0> Nat countIf(F0 &&p) const;
  };

  static inline const Nat depth_limit =
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
  static bool even(const Nat &n);
  static bool odd(const Nat &n);
};

struct Tally {
  struct held {
    Bag::bag<Nat> unhold;
  };

  static Nat bump(const Nat &n);
};

Bag::bag<Nat> roundtrip(Bag::bag<Nat> b);
bool count_odd_is(const Bag::bag<Nat> &b, const Nat &n);
const Nat limit = Bag::depth_limit;
Bag::bag<Nat> round(Bag::bag<Nat> x0_);

template <typename A>
template <typename F0>
Nat Bag::bag<A>::countIf(F0 &&p) const {
  const typename Bag::template bag<A> *_self = this;

  /// CraneEnter: captures varying parameters for each recursive call.
  struct CraneEnter {
    const typename Bag::template bag<A> *_self;
  };

  /// CraneCont1: resumes after recursive call, then processes rest.
  struct CraneCont1 {};

  using CraneFrame = std::variant<CraneEnter, CraneCont1>;
  Nat _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{_self});
  /// Loopified countIf: CraneEnter -> CraneCont1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const typename Bag::template bag<A> *_self = _f._self;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename Bag::bag<A>::Empty>(_sv.v())) {
        _result = Nat::o();
      } else {
        const auto &[a0, a1] = std::get<typename Bag::bag<A>::Add>(_sv.v());
        if (p(a0)) {
          _stack.emplace_back(CraneCont1{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont1>(_frame));
      _result = Tally::bump(std::move(_result));
    }
  }
  return _result;
}

#endif // INCLUDED_NESTED_OWNER_TWO_TEMPLATE_HEADS
