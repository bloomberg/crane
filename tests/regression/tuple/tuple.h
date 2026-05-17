#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

#include <memory>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> a0;
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

  Nat(Nat &&_other) : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
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
        _dst->v_ = S{_alt.a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
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
};

template <typename A, typename B> struct Prod {
  // TYPES
  struct Pair {
    A a0;
    B a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Prod() {}

  explicit Prod(Pair _v) : v_(std::move(_v)) {}

  Prod(const Prod<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

  Prod(Prod<A, B> &&_other) : v_(std::move(_other.v_)) {}

  Prod<A, B> &operator=(const Prod<A, B> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Prod<A, B> &operator=(Prod<A, B> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Prod<A, B> clone() const {
    const auto &[a0, a1] = std::get<Pair>(this->v());
    return Prod<A, B>(Pair{a0, a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Prod(const Prod<_U0, _U1> &_other) {
    const auto &[a0, a1] = std::get<typename Prod<_U0, _U1>::Pair>(_other.v());
    this->v_ = Pair{A(a0), B(a1)};
  }

  static Prod<A, B> pair(A a0, B a1) {
    return Prod(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Tuple {
  template <typename a, typename b> using pair = Prod<a, b>;

  template <typename T1, typename T2>
  static Prod<T1, T2> make_pair(T1 a, T2 b) {
    return Prod<T1, T2>::pair(a, b);
  }

  template <typename T1, typename T2> static T1 fst(const Prod<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return a0;
  }

  template <typename T1, typename T2> static T2 snd(const Prod<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return a1;
  }

  template <typename T1, typename T2>
  static Prod<T2, T1> swap(const Prod<T1, T2> &p) {
    const auto &[a0, a1] = std::get<typename Prod<T1, T2>::Pair>(p.v());
    return Prod<T2, T1>::pair(a1, a0);
  }

  static inline const Prod<Nat, Nat> test_pair =
      make_pair<Nat, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
  static inline const Nat test_fst = fst<Nat, Nat>(test_pair);
  static inline const Prod<Nat, Nat> test_swap = swap<Nat, Nat>(test_pair);
};

#endif // INCLUDED_TUPLE
