#ifndef INCLUDED_MUTUAL_TMC_LOOPIFY
#define INCLUDED_MUTUAL_TMC_LOOPIFY

#include "small_vector.h"
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

struct MutualTmcLoopify {
  /// Mutual recursion whose recursive calls are under a constructor (TMC).
  /// Crane Loopify emits a _Frame worklist, but the body of the sibling
  /// odds is inlined as an immediately-invoked lambda that still calls
  /// evens(...) recursively, so the while loop runs exactly once and the
  /// real recursion is unchanged.  Compiles, then overflows the stack under
  /// ASan at moderate depth.
  struct mylist {
    // TYPES
    struct Mnil {};

    struct Mcons {
      Nat a0;
      std::shared_ptr<mylist> a1;
    };

    using variant_t = std::variant<Mnil, Mcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mnil _v) : v_(_v) {}

    explicit mylist(Mcons _v) : v_(std::move(_v)) {}

    static mylist mnil() { return mylist(Mnil{}); }

    static mylist mcons(Nat a0, mylist a1) {
      return mylist(
          Mcons{std::move(a0), std::make_shared<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mcons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static mylist evens(Nat n);
  static mylist odds(Nat n);
  static Nat len(const mylist &l);
};

#endif // INCLUDED_MUTUAL_TMC_LOOPIFY
