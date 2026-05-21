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

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) noexcept : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.n ? std::make_shared<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.n) {
          _stack.push_back({_alt.n.get(), _dst_alt.n.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat n) { return Nat(S{std::make_shared<Nat>(std::move(n))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.n) {
          _stack.push_back(std::move(_alt.n));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
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
