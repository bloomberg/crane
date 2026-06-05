#ifndef INCLUDED_ROCQ_BUG_5177
#define INCLUDED_ROCQ_BUG_5177

#include <concepts>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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
    std::vector<std::shared_ptr<Nat>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename M>
concept T = requires { typename M::t; };
template <typename M>
concept A = requires {
  typename M::t1;
  typename M::t2;
  {
    M::bar(std::declval<typename M::MT::t>(), std::declval<typename M::t1>())
  } -> std::same_as<typename M::t2>;
};

struct RocqBug5177 {
  template <T MT> struct MakeA {
    using t1 = Nat;
    using t2 = Nat;

    static t1 bar(typename MT::t, Nat x) { return x; }
  };
};

#endif // INCLUDED_ROCQ_BUG_5177
