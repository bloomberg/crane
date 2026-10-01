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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MutualTmcLoopify {
  /// Mutual recursion whose recursive calls are under a constructor (TMC).
  ///
  /// Loopification inlines the sibling odds into evens as an
  /// immediately-invoked lambda, which still calls evens.  That body is
  /// adopted as a second entry point of evens's frame machine, so both halves
  /// of the mutual recursion push onto one stack and the extracted evens has
  /// no C++ self-call -- it survives the depth this test exercises.
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
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist> {
        if (auto *_alt = std::get_if<Mcons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
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

  static mylist evens(const Nat &n);
  static mylist odds(const Nat &n);
  static Nat len(const mylist &l);
};

#endif // INCLUDED_MUTUAL_TMC_LOOPIFY
