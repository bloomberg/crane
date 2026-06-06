#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  /// Peano natural numbers: O is zero and S n is the successor of n.
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> n;
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

  static Nat s(Nat n) { return Nat(S{std::make_shared<Nat>(std::move(n))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->n) {
          _stack.push_back(std::move(_alt->n));
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  T1 nat_rect(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[n1] = std::get<typename Nat::S>(this->v());
      return f0(*n1, n1->template nat_rect<T1>(f, f0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  T1 nat_rec(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[n1] = std::get<typename Nat::S>(this->v());
      return f0(*n1, n1->template nat_rec<T1>(f, f0));
    }
  }

  /// add m n computes the sum of m and n by recursion on m.
  Nat add(Nat n) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return n;
    } else {
      const auto &[n0] = std::get<typename Nat::S>(this->v());
      return Nat::s(n0->add(std::move(n)));
    }
  }

  /// Convert a Peano nat to a machine int.
  int nat_to_int() const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return 0;
    } else {
      const auto &[n0] = std::get<typename Nat::S>(this->v());
      return 1 + n0->nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT
