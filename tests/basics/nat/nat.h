#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  /// Peano natural numbers: O is zero and S n is the successor of n.
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_n;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        const auto &_alt = std::get<O>(_src->v());
        _dst->d_v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->d_v_ = S{_alt.d_n ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->d_v_);
        if (_alt.d_n)
          _stack.push_back({_alt.d_n.get(), _dst_alt.d_n.get()});
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat n) { return Nat(S{std::make_unique<Nat>(std::move(n))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack;
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.d_v_)) {
        auto &_alt = std::get<S>(_node.d_v_);
        if (_alt.d_n)
          _stack.push_back(std::move(_alt.d_n));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, Nat, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return f0(*(d_n), (*(d_n)).template nat_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, Nat, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return f;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return f0(*(d_n), (*(d_n)).template nat_rec<T1>(f, f0));
    }
  }

  /// add m n computes the sum of m and n by recursion on m.
  Nat add(Nat n) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return n;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return Nat::s((*(d_n)).add(std::move(n)));
    }
  }

  /// Convert a Peano nat to a machine int.
  int nat_to_int() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return 0;
    } else {
      const auto &[d_n] = std::get<typename Nat::S>(_sv.v());
      return 1 + (*(d_n)).nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT
