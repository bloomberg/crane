#ifndef INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
#define INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return true;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (f(d_a0) && (*(d_a1)).forallb(f));
    }
  }

  template <typename T1, MapsTo<T1, T1, t_A> F0>
  T1 fold_left(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).template fold_left<T1>(f, f(a0, d_a0));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D1 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D2 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D3 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D4 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D5 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D6 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D7 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D8 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D9 {
    std::unique_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : d_v_(_v) {}

  explicit Uint(D0 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D1 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D2 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D3 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D4 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D5 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D6 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D7 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D8 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D9 _v) : d_v_(std::move(_v)) {}

  Uint(const Uint &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint(Uint &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint &operator=(const Uint &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint &operator=(Uint &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return Uint(Nil{});
    } else if (std::holds_alternative<D0>(_sv.v())) {
      const auto &[d_a0] = std::get<D0>(_sv.v());
      return Uint(D0{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D1>(_sv.v())) {
      const auto &[d_a0] = std::get<D1>(_sv.v());
      return Uint(D1{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D2>(_sv.v())) {
      const auto &[d_a0] = std::get<D2>(_sv.v());
      return Uint(D2{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D3>(_sv.v())) {
      const auto &[d_a0] = std::get<D3>(_sv.v());
      return Uint(D3{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D4>(_sv.v())) {
      const auto &[d_a0] = std::get<D4>(_sv.v());
      return Uint(D4{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D5>(_sv.v())) {
      const auto &[d_a0] = std::get<D5>(_sv.v());
      return Uint(D5{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D6>(_sv.v())) {
      const auto &[d_a0] = std::get<D6>(_sv.v());
      return Uint(D6{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D7>(_sv.v())) {
      const auto &[d_a0] = std::get<D7>(_sv.v());
      return Uint(D7{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D8>(_sv.v())) {
      const auto &[d_a0] = std::get<D8>(_sv.v());
      return Uint(D8{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    } else {
      const auto &[d_a0] = std::get<D9>(_sv.v());
      return Uint(D9{d_a0 ? std::make_unique<Uint>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint nil() { return Uint(Nil{}); }

  __attribute__((pure)) static Uint d0(Uint a0) {
    return Uint(D0{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d1(Uint a0) {
    return Uint(D1{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d2(Uint a0) {
    return Uint(D2{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d3(Uint a0) {
    return Uint(D3{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d4(Uint a0) {
    return Uint(D4{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d5(Uint a0) {
    return Uint(D5{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d6(Uint a0) {
    return Uint(D6{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d7(Uint a0) {
    return Uint(D7{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d8(Uint a0) {
    return Uint(D8{std::make_unique<Uint>(std::move(a0))});
  }

  __attribute__((pure)) static Uint d9(Uint a0) {
    return Uint(D9{std::make_unique<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint() {
    std::vector<std::unique_ptr<Uint>> _stack;
    auto _drain = [&](Uint &_node) {
      if (std::holds_alternative<D0>(_node.d_v_)) {
        auto &_alt = std::get<D0>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D1>(_node.d_v_)) {
        auto &_alt = std::get<D1>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D2>(_node.d_v_)) {
        auto &_alt = std::get<D2>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D3>(_node.d_v_)) {
        auto &_alt = std::get<D3>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D4>(_node.d_v_)) {
        auto &_alt = std::get<D4>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D5>(_node.d_v_)) {
        auto &_alt = std::get<D5>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D6>(_node.d_v_)) {
        auto &_alt = std::get<D6>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D7>(_node.d_v_)) {
        auto &_alt = std::get<D7>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D8>(_node.d_v_)) {
        auto &_alt = std::get<D8>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D9>(_node.d_v_)) {
        auto &_alt = std::get<D9>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Da {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Db {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::unique_ptr<Uint0> d_a0;
  };

  struct De {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Df {
    std::unique_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : d_v_(_v) {}

  explicit Uint0(D10 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Da _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Db _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : d_v_(std::move(_v)) {}

  explicit Uint0(De _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Df _v) : d_v_(std::move(_v)) {}

  Uint0(const Uint0 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint0(Uint0 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint0 &operator=(const Uint0 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint0 &operator=(Uint0 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint0 clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil0>(_sv.v())) {
      return Uint0(Nil0{});
    } else if (std::holds_alternative<D10>(_sv.v())) {
      const auto &[d_a0] = std::get<D10>(_sv.v());
      return Uint0(
          D10{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D11>(_sv.v())) {
      const auto &[d_a0] = std::get<D11>(_sv.v());
      return Uint0(
          D11{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D12>(_sv.v())) {
      const auto &[d_a0] = std::get<D12>(_sv.v());
      return Uint0(
          D12{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D13>(_sv.v())) {
      const auto &[d_a0] = std::get<D13>(_sv.v());
      return Uint0(
          D13{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D14>(_sv.v())) {
      const auto &[d_a0] = std::get<D14>(_sv.v());
      return Uint0(
          D14{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D15>(_sv.v())) {
      const auto &[d_a0] = std::get<D15>(_sv.v());
      return Uint0(
          D15{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D16>(_sv.v())) {
      const auto &[d_a0] = std::get<D16>(_sv.v());
      return Uint0(
          D16{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D17>(_sv.v())) {
      const auto &[d_a0] = std::get<D17>(_sv.v());
      return Uint0(
          D17{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D18>(_sv.v())) {
      const auto &[d_a0] = std::get<D18>(_sv.v());
      return Uint0(
          D18{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<D19>(_sv.v())) {
      const auto &[d_a0] = std::get<D19>(_sv.v());
      return Uint0(
          D19{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Da>(_sv.v())) {
      const auto &[d_a0] = std::get<Da>(_sv.v());
      return Uint0(Da{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Db>(_sv.v())) {
      const auto &[d_a0] = std::get<Db>(_sv.v());
      return Uint0(Db{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Dc>(_sv.v())) {
      const auto &[d_a0] = std::get<Dc>(_sv.v());
      return Uint0(Dc{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<Dd>(_sv.v())) {
      const auto &[d_a0] = std::get<Dd>(_sv.v());
      return Uint0(Dd{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<De>(_sv.v())) {
      const auto &[d_a0] = std::get<De>(_sv.v());
      return Uint0(De{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    } else {
      const auto &[d_a0] = std::get<Df>(_sv.v());
      return Uint0(Df{d_a0 ? std::make_unique<Uint0>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint0 nil0() { return Uint0(Nil0{}); }

  __attribute__((pure)) static Uint0 d10(Uint0 a0) {
    return Uint0(D10{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_unique<Uint0>(std::move(a0))});
  }

  __attribute__((pure)) static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_unique<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint0() {
    std::vector<std::unique_ptr<Uint0>> _stack;
    auto _drain = [&](Uint0 &_node) {
      if (std::holds_alternative<D10>(_node.d_v_)) {
        auto &_alt = std::get<D10>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D11>(_node.d_v_)) {
        auto &_alt = std::get<D11>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D12>(_node.d_v_)) {
        auto &_alt = std::get<D12>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D13>(_node.d_v_)) {
        auto &_alt = std::get<D13>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D14>(_node.d_v_)) {
        auto &_alt = std::get<D14>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D15>(_node.d_v_)) {
        auto &_alt = std::get<D15>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D16>(_node.d_v_)) {
        auto &_alt = std::get<D16>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D17>(_node.d_v_)) {
        auto &_alt = std::get<D17>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D18>(_node.d_v_)) {
        auto &_alt = std::get<D18>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D19>(_node.d_v_)) {
        auto &_alt = std::get<D19>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Da>(_node.d_v_)) {
        auto &_alt = std::get<Da>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Db>(_node.d_v_)) {
        auto &_alt = std::get<Db>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Dc>(_node.d_v_)) {
        auto &_alt = std::get<Dc>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Dd>(_node.d_v_)) {
        auto &_alt = std::get<Dd>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<De>(_node.d_v_)) {
        auto &_alt = std::get<De>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Df>(_node.d_v_)) {
        auto &_alt = std::get<Df>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint d_u;
  };

  struct UIntHexadecimal {
    Uint0 d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  Uint1(const Uint1 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint1(Uint1 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint1 &operator=(const Uint1 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint1 &operator=(Uint1 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Uint1 clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<UIntDecimal>(_sv.v())) {
      const auto &[d_u] = std::get<UIntDecimal>(_sv.v());
      return Uint1(UIntDecimal{d_u.clone()});
    } else {
      const auto &[d_u] = std::get<UIntHexadecimal>(_sv.v());
      return Uint1(UIntHexadecimal{d_u.clone()});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint1 uintdecimal(Uint u) {
    return Uint1(UIntDecimal{std::move(u)});
  }

  __attribute__((pure)) static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Nat {
  __attribute__((pure)) static unsigned int tail_add(const unsigned int &n,
                                                     unsigned int m);
  __attribute__((pure)) static unsigned int
  tail_addmul(unsigned int r, const unsigned int &n, const unsigned int &m);
  __attribute__((pure)) static unsigned int tail_mul(const unsigned int &n,
                                                     const unsigned int &m);
  __attribute__((pure)) static unsigned int of_uint_acc(const Uint &d,
                                                        unsigned int acc);
  __attribute__((pure)) static unsigned int of_uint(const Uint &d);
  __attribute__((pure)) static unsigned int of_hex_uint_acc(const Uint0 &d,
                                                            unsigned int acc);
  __attribute__((pure)) static unsigned int of_hex_uint(const Uint0 &d);
  __attribute__((pure)) static unsigned int of_num_uint(const Uint1 &d);
};

struct ValidatedPumpDeliveryTraceCase {
  struct Mg_dL {
    unsigned int mg_dL_val;

    // ACCESSORS
    __attribute__((pure)) Mg_dL clone() const {
      return Mg_dL{(*(this)).mg_dL_val};
    }
  };

  struct Grams {
    unsigned int grams_val;

    // ACCESSORS
    __attribute__((pure)) Grams clone() const {
      return Grams{(*(this)).grams_val};
    }
  };

  using Carbs_g = Grams;
  using Minutes = unsigned int;
  using DIA_minutes = unsigned int;
  using Insulin_twentieth = unsigned int;
  static inline const unsigned int ONE_UNIT = 20u;
  static inline const unsigned int BG_LEVEL2_HYPO = 54u;
  static inline const unsigned int BG_HYPO = 70u;
  static inline const unsigned int BG_HYPER = 180u;
  static inline const unsigned int BG_METER_MIN = 20u;
  static inline const unsigned int BG_METER_MAX = 600u;
  static inline const unsigned int CARBS_SANITY_MAX = 200u;
  __attribute__((pure)) static bool bg_in_meter_range(const Mg_dL &bg);
  __attribute__((pure)) static bool carbs_reasonable(const Grams &carbs);

  struct Config {
    unsigned int cfg_bg_rise_per_gram;
    unsigned int cfg_conservative_cob_absorption_percent;
    unsigned int cfg_suspend_threshold_mg_dl;
    unsigned int cfg_stacking_warning_threshold_min;
    unsigned int cfg_iob_high_threshold_twentieths;

    // ACCESSORS
    __attribute__((pure)) Config clone() const {
      return Config{(*(this)).cfg_bg_rise_per_gram,
                    (*(this)).cfg_conservative_cob_absorption_percent,
                    (*(this)).cfg_suspend_threshold_mg_dl,
                    (*(this)).cfg_stacking_warning_threshold_min,
                    (*(this)).cfg_iob_high_threshold_twentieths};
    }
  };

  static inline const Config default_config = Config{4u, 30u, 80u, 60u, 200u};
  enum class ActivityState {
    e_ACTIVITY_NORMAL,
    e_ACTIVITY_LIGHTEXERCISE,
    e_ACTIVITY_MODERATEEXERCISE,
    e_ACTIVITY_INTENSEEXERCISE,
    e_ACTIVITY_ILLNESS,
    e_ACTIVITY_STRESS
  };

  template <typename T1>
  static T1 ActivityState_rect(const T1 f, const T1 f0, const T1 f1,
                               const T1 f2, const T1 f3, const T1 f4,
                               const ActivityState a) {
    switch (a) {
    case ActivityState::e_ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::e_ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::e_ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ActivityState_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                              const T1 f3, const T1 f4, const ActivityState a) {
    switch (a) {
    case ActivityState::e_ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::e_ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::e_ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::e_ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::e_ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::e_ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  isf_activity_modifier(const ActivityState state);
  __attribute__((pure)) static unsigned int
  icr_activity_modifier(const ActivityState state);

  struct FaultStatus {
    // TYPES
    struct Fault_None {};

    struct Fault_Occlusion {};

    struct Fault_LowReservoir {
      unsigned int d_a0;
    };

    struct Fault_BatteryLow {};

    struct Fault_Unknown {};

    using variant_t =
        std::variant<Fault_None, Fault_Occlusion, Fault_LowReservoir,
                     Fault_BatteryLow, Fault_Unknown>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    FaultStatus() {}

    explicit FaultStatus(Fault_None _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_Occlusion _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_LowReservoir _v) : d_v_(std::move(_v)) {}

    explicit FaultStatus(Fault_BatteryLow _v) : d_v_(_v) {}

    explicit FaultStatus(Fault_Unknown _v) : d_v_(_v) {}

    FaultStatus(const FaultStatus &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    FaultStatus(FaultStatus &&_other) : d_v_(std::move(_other.d_v_)) {}

    FaultStatus &operator=(const FaultStatus &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    FaultStatus &operator=(FaultStatus &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) FaultStatus clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Fault_None>(_sv.v())) {
        return FaultStatus(Fault_None{});
      } else if (std::holds_alternative<Fault_Occlusion>(_sv.v())) {
        return FaultStatus(Fault_Occlusion{});
      } else if (std::holds_alternative<Fault_LowReservoir>(_sv.v())) {
        const auto &[d_a0] = std::get<Fault_LowReservoir>(_sv.v());
        return FaultStatus(Fault_LowReservoir{d_a0});
      } else if (std::holds_alternative<Fault_BatteryLow>(_sv.v())) {
        return FaultStatus(Fault_BatteryLow{});
      } else {
        return FaultStatus(Fault_Unknown{});
      }
    }

    // CREATORS
    __attribute__((pure)) static FaultStatus fault_none() {
      return FaultStatus(Fault_None{});
    }

    __attribute__((pure)) static FaultStatus fault_occlusion() {
      return FaultStatus(Fault_Occlusion{});
    }

    __attribute__((pure)) static FaultStatus
    fault_lowreservoir(unsigned int a0) {
      return FaultStatus(Fault_LowReservoir{std::move(a0)});
    }

    __attribute__((pure)) static FaultStatus fault_batterylow() {
      return FaultStatus(Fault_BatteryLow{});
    }

    __attribute__((pure)) static FaultStatus fault_unknown() {
      return FaultStatus(Fault_Unknown{});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool fault_blocks_bolus() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename FaultStatus::Fault_None>(_sv.v())) {
        return false;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(_sv.v())) {
        const auto &[d_a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(_sv.v());
        return d_a0 < 10u;
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     _sv.v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F2>
    T1 FaultStatus_rec(const T1 f, const T1 f0, F2 &&f1, const T1 f2,
                       const T1 f3) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename FaultStatus::Fault_None>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename FaultStatus::Fault_Occlusion>(
                     _sv.v())) {
        return f0;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(_sv.v())) {
        const auto &[d_a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     _sv.v())) {
        return f2;
      } else {
        return f3;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F2>
    T1 FaultStatus_rect(const T1 f, const T1 f0, F2 &&f1, const T1 f2,
                        const T1 f3) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename FaultStatus::Fault_None>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename FaultStatus::Fault_Occlusion>(
                     _sv.v())) {
        return f0;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(_sv.v())) {
        const auto &[d_a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(_sv.v());
        return f1(d_a0);
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     _sv.v())) {
        return f2;
      } else {
        return f3;
      }
    }
  };
  enum class InsulinType {
    e_INSULIN_HUMALOG,
    e_INSULIN_ASPART,
    e_INSULIN_LISPRO
  };

  template <typename T1>
  static T1 InsulinType_rect(const T1 f, const T1 f0, const T1 f1,
                             const InsulinType i) {
    switch (i) {
    case InsulinType::e_INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::e_INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::e_INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 InsulinType_rec(const T1 f, const T1 f0, const T1 f1,
                            const InsulinType i) {
    switch (i) {
    case InsulinType::e_INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::e_INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::e_INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static Minutes peak_time(const InsulinType itype,
                                                 const unsigned int &_x);

  struct BolusEvent {
    unsigned int be_dose_twentieths;
    Minutes be_time_minutes;

    // ACCESSORS
    __attribute__((pure)) BolusEvent clone() const {
      return BolusEvent{(*(this)).be_dose_twentieths,
                        (*(this)).be_time_minutes};
    }
  };

  __attribute__((pure)) static unsigned int div_ceil(const unsigned int &a,
                                                     const unsigned int &b);
  __attribute__((pure)) static bool event_time_valid(const unsigned int &now,
                                                     const BolusEvent &event);
  __attribute__((pure)) static bool
  history_times_valid(const unsigned int &now, const List<BolusEvent> &events);
  __attribute__((pure)) static bool
  history_sorted_from(const unsigned int &prev, const List<BolusEvent> &events);
  __attribute__((pure)) static bool
  history_sorted_desc(const List<BolusEvent> &events);
  __attribute__((pure)) static bool
  history_valid(const unsigned int &now, const List<BolusEvent> &events);
  __attribute__((pure)) static unsigned int
  bilinear_iob_fraction(const unsigned int &elapsed, const unsigned int &dia,
                        const InsulinType itype);
  __attribute__((pure)) static Insulin_twentieth
  bilinear_iob_from_bolus(const unsigned int &now, const BolusEvent &event,
                          const unsigned int &dia, const InsulinType itype);
  __attribute__((pure)) static Insulin_twentieth
  total_bilinear_iob(const unsigned int &now, const List<BolusEvent> &events,
                     const unsigned int &dia, const InsulinType itype);
  __attribute__((pure)) static Mg_dL apply_sensor_margin(Mg_dL bg,
                                                         const Mg_dL &target);
  __attribute__((pure)) static unsigned int
  adjusted_isf_tenths(const Mg_dL &bg, unsigned int base_isf_tenths);
  __attribute__((pure)) static Insulin_twentieth
  correction_twentieths_full(const unsigned int &_x, const Mg_dL &current_bg,
                             const Mg_dL &target_bg,
                             const unsigned int &base_isf_tenths);
  __attribute__((pure)) static Insulin_twentieth
  apply_reverse_correction_twentieths(unsigned int carb,
                                      const Mg_dL &current_bg,
                                      const Mg_dL &target_bg,
                                      const unsigned int &isf_tenths);

  struct SuspendDecision {
    // TYPES
    struct Suspend_None {};

    struct Suspend_Reduce {
      Insulin_twentieth d_a0;
    };

    struct Suspend_Withhold {};

    using variant_t =
        std::variant<Suspend_None, Suspend_Reduce, Suspend_Withhold>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    SuspendDecision() {}

    explicit SuspendDecision(Suspend_None _v) : d_v_(_v) {}

    explicit SuspendDecision(Suspend_Reduce _v) : d_v_(std::move(_v)) {}

    explicit SuspendDecision(Suspend_Withhold _v) : d_v_(_v) {}

    SuspendDecision(const SuspendDecision &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    SuspendDecision(SuspendDecision &&_other) : d_v_(std::move(_other.d_v_)) {}

    SuspendDecision &operator=(const SuspendDecision &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    SuspendDecision &operator=(SuspendDecision &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) SuspendDecision clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Suspend_None>(_sv.v())) {
        return SuspendDecision(Suspend_None{});
      } else if (std::holds_alternative<Suspend_Reduce>(_sv.v())) {
        const auto &[d_a0] = std::get<Suspend_Reduce>(_sv.v());
        return SuspendDecision(Suspend_Reduce{d_a0});
      } else {
        return SuspendDecision(Suspend_Withhold{});
      }
    }

    // CREATORS
    __attribute__((pure)) static SuspendDecision suspend_none() {
      return SuspendDecision(Suspend_None{});
    }

    __attribute__((pure)) static SuspendDecision
    suspend_reduce(Insulin_twentieth a0) {
      return SuspendDecision(Suspend_Reduce{std::move(a0)});
    }

    __attribute__((pure)) static SuspendDecision suspend_withhold() {
      return SuspendDecision(Suspend_Withhold{});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 SuspendDecision_rect(const T1 f, F1 &&f0, const T1 f1,
                                 const SuspendDecision &s) {
    if (std::holds_alternative<typename SuspendDecision::Suspend_None>(s.v())) {
      return f;
    } else if (std::holds_alternative<typename SuspendDecision::Suspend_Reduce>(
                   s.v())) {
      const auto &[d_a0] =
          std::get<typename SuspendDecision::Suspend_Reduce>(s.v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 SuspendDecision_rec(const T1 f, F1 &&f0, const T1 f1,
                                const SuspendDecision &s) {
    if (std::holds_alternative<typename SuspendDecision::Suspend_None>(s.v())) {
      return f;
    } else if (std::holds_alternative<typename SuspendDecision::Suspend_Reduce>(
                   s.v())) {
      const auto &[d_a0] =
          std::get<typename SuspendDecision::Suspend_Reduce>(s.v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  __attribute__((pure)) static unsigned int
  predict_bg_drop_tenths(const unsigned int &iob_twentieths,
                         const unsigned int &isf_tenths);
  __attribute__((pure)) static unsigned int
  conservative_cob_rise(const Config &cfg, const unsigned int &cob_grams);
  __attribute__((pure)) static unsigned int
  predicted_eventual_bg_tenths(const Config &cfg, const Mg_dL &current_bg,
                               const unsigned int &iob_twentieths,
                               const unsigned int &cob_grams,
                               const unsigned int &isf_tenths);
  __attribute__((pure)) static SuspendDecision suspend_check_tenths_with_cob(
      const Config &cfg, const Mg_dL &current_bg,
      const unsigned int &iob_twentieths, const unsigned int &cob_grams,
      const unsigned int &isf_tenths, const unsigned int &proposed);
  __attribute__((pure)) static Insulin_twentieth
  apply_suspend(unsigned int proposed, const SuspendDecision &decision);
  __attribute__((pure)) static Insulin_twentieth
  pediatric_max_twentieths(const unsigned int &weight_kg);
  __attribute__((pure)) static Insulin_twentieth
  cap_pediatric(unsigned int bolus, const unsigned int &weight_kg);

  struct PrecisionParams {
    unsigned int prec_icr_tenths;
    unsigned int prec_isf_tenths;
    Mg_dL prec_target_bg;
    DIA_minutes prec_dia;
    InsulinType prec_insulin_type;

    // ACCESSORS
    __attribute__((pure)) PrecisionParams clone() const {
      return PrecisionParams{(*(this)).prec_icr_tenths,
                             (*(this)).prec_isf_tenths,
                             (*(this)).prec_target_bg.clone(),
                             (*(this)).prec_dia, (*(this)).prec_insulin_type};
    }
  };

  __attribute__((pure)) static bool prec_params_valid(const PrecisionParams &p);

  struct PrecisionInput {
    Carbs_g pi_carbs_g;
    Mg_dL pi_current_bg;
    Minutes pi_now;
    List<BolusEvent> pi_bolus_history;
    ActivityState pi_activity;
    bool pi_use_sensor_margin;
    FaultStatus pi_fault;
    std::optional<unsigned int> pi_weight_kg;

    // ACCESSORS
    __attribute__((pure)) PrecisionInput clone() const {
      return PrecisionInput{
          (*(this)).pi_carbs_g,       (*(this)).pi_current_bg.clone(),
          (*(this)).pi_now,           (*(this)).pi_bolus_history.clone(),
          (*(this)).pi_activity,      (*(this)).pi_use_sensor_margin,
          (*(this)).pi_fault.clone(), (*(this)).pi_weight_kg};
    }
  };

  __attribute__((pure)) static Insulin_twentieth
  carb_bolus_twentieths(const unsigned int &carbs_g,
                        const unsigned int &icr_tenths);
  __attribute__((pure)) static Insulin_twentieth
  calculate_precision_bolus(const PrecisionInput &input,
                            const PrecisionParams &params);
  __attribute__((pure)) static bool time_reasonable(const unsigned int &now);
  __attribute__((pure)) static bool
  history_extraction_safe(const List<BolusEvent> &events);
  __attribute__((pure)) static unsigned int
  iob_high_threshold(const Config &cfg);
  __attribute__((pure)) static bool
  iob_dangerously_high(const unsigned int &iob);

  struct PrecisionResult {
    // TYPES
    struct PrecOK {
      Insulin_twentieth d_a0;
      bool d_a1;
    };

    struct PrecError {
      unsigned int d_a0;
    };

    using variant_t = std::variant<PrecOK, PrecError>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    PrecisionResult() {}

    explicit PrecisionResult(PrecOK _v) : d_v_(std::move(_v)) {}

    explicit PrecisionResult(PrecError _v) : d_v_(std::move(_v)) {}

    PrecisionResult(const PrecisionResult &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    PrecisionResult(PrecisionResult &&_other) : d_v_(std::move(_other.d_v_)) {}

    PrecisionResult &operator=(const PrecisionResult &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    PrecisionResult &operator=(PrecisionResult &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) PrecisionResult clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<PrecOK>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<PrecOK>(_sv.v());
        return PrecisionResult(PrecOK{d_a0, d_a1});
      } else {
        const auto &[d_a0] = std::get<PrecError>(_sv.v());
        return PrecisionResult(PrecError{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static PrecisionResult precok(Insulin_twentieth a0,
                                                        bool a1) {
      return PrecisionResult(PrecOK{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static PrecisionResult precerror(unsigned int a0) {
      return PrecisionResult(PrecError{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool result_modified() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename PrecisionResult::PrecOK>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename PrecisionResult::PrecOK>(_sv.v());
        return d_a1;
      } else {
        return false;
      }
    }

    __attribute__((pure)) unsigned int precision_result_code() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename PrecisionResult::PrecOK>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0] =
            std::get<typename PrecisionResult::PrecError>(_sv.v());
        return d_a0;
      }
    }
  };

  template <typename T1, MapsTo<T1, unsigned int, bool> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 PrecisionResult_rect(F0 &&f, F1 &&f0, const PrecisionResult &p) {
    if (std::holds_alternative<typename PrecisionResult::PrecOK>(p.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename PrecisionResult::PrecOK>(p.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0] = std::get<typename PrecisionResult::PrecError>(p.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, bool> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 PrecisionResult_rec(F0 &&f, F1 &&f0, const PrecisionResult &p) {
    if (std::holds_alternative<typename PrecisionResult::PrecOK>(p.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename PrecisionResult::PrecOK>(p.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0] = std::get<typename PrecisionResult::PrecError>(p.v());
      return f0(d_a0);
    }
  }

  static inline const unsigned int prec_error_invalid_params = 1u;
  static inline const unsigned int prec_error_invalid_input = 2u;
  static inline const unsigned int prec_error_hypo = 3u;
  static inline const unsigned int prec_error_invalid_history = 4u;
  static inline const unsigned int prec_error_invalid_time = 5u;
  static inline const unsigned int prec_error_stacking = 6u;
  static inline const unsigned int prec_error_fault = 7u;
  static inline const unsigned int prec_error_tdd_exceeded = 8u;
  static inline const unsigned int prec_error_iob_high = 9u;
  static inline const unsigned int prec_error_extraction_unsafe = 10u;
  __attribute__((pure)) static bool
  bolus_too_soon(const unsigned int &now, const List<BolusEvent> &history);
  __attribute__((pure)) static Insulin_twentieth cap_twentieths(unsigned int t);
  __attribute__((pure)) static PrecisionResult
  validated_precision_bolus(PrecisionInput input,
                            const PrecisionParams &params);
  __attribute__((pure)) static std::optional<Insulin_twentieth>
  prec_result_twentieths(const PrecisionResult &r);

  struct MmolPrecisionInput {
    Carbs_g mpi_carbs_g;
    unsigned int mpi_current_bg_mmol_tenths;
    Minutes mpi_now;
    List<BolusEvent> mpi_bolus_history;
    ActivityState mpi_activity;
    bool mpi_use_sensor_margin;
    FaultStatus mpi_fault;
    std::optional<unsigned int> mpi_weight_kg;

    // ACCESSORS
    __attribute__((pure)) MmolPrecisionInput clone() const {
      return MmolPrecisionInput{
          (*(this)).mpi_carbs_g,       (*(this)).mpi_current_bg_mmol_tenths,
          (*(this)).mpi_now,           (*(this)).mpi_bolus_history.clone(),
          (*(this)).mpi_activity,      (*(this)).mpi_use_sensor_margin,
          (*(this)).mpi_fault.clone(), (*(this)).mpi_weight_kg};
    }
  };

  __attribute__((pure)) static unsigned int
  mmol_tenths_to_mg_dL(const unsigned int &mmol_tenths);
  __attribute__((pure)) static PrecisionInput
  convert_mmol_input(const MmolPrecisionInput &input);
  __attribute__((pure)) static PrecisionResult
  validated_mmol_bolus(const MmolPrecisionInput &input,
                       const PrecisionParams &params);
  enum class RoundingMode {
    e_ROUNDTWENTIETH,
    e_ROUNDTENTH,
    e_ROUNDHALF,
    e_ROUNDUNIT
  };

  template <typename T1>
  static T1 RoundingMode_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                              const RoundingMode r) {
    switch (r) {
    case RoundingMode::e_ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::e_ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::e_ROUNDHALF: {
      return f1;
    }
    case RoundingMode::e_ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 RoundingMode_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                             const RoundingMode r) {
    switch (r) {
    case RoundingMode::e_ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::e_ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::e_ROUNDHALF: {
      return f1;
    }
    case RoundingMode::e_ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static unsigned int
  round_down_to_increment(unsigned int t, const unsigned int &increment);
  __attribute__((pure)) static Insulin_twentieth
  apply_rounding(const RoundingMode mode, unsigned int t);
  __attribute__((pure)) static std::optional<Insulin_twentieth>
  final_delivery(const RoundingMode mode, const PrecisionResult &result);

  struct PumpState {
    unsigned int ps_reservoir_twentieths;
    unsigned int ps_basal_rate_hundredths;
    Minutes ps_last_bolus_time;
    bool ps_occlusion_detected;
    unsigned int ps_battery_percent;

    // ACCESSORS
    __attribute__((pure)) PumpState clone() const {
      return PumpState{
          (*(this)).ps_reservoir_twentieths, (*(this)).ps_basal_rate_hundredths,
          (*(this)).ps_last_bolus_time, (*(this)).ps_occlusion_detected,
          (*(this)).ps_battery_percent};
    }
  };

  __attribute__((pure)) static bool pump_can_deliver(const PumpState &state,
                                                     const unsigned int &dose);
  __attribute__((pure)) static unsigned int
  reservoir_after_bolus(const PumpState &state, const unsigned int &dose);
  __attribute__((pure)) static unsigned int
  option_nat_default(const std::optional<unsigned int> &x, unsigned int d);
  __attribute__((pure)) static bool
  pump_accepts_result(const PumpState &pump, const RoundingMode mode,
                      const PrecisionResult &r);
  __attribute__((pure)) static unsigned int
  pump_reservoir_after_result(const PumpState &pump, const RoundingMode mode,
                              const PrecisionResult &r);
  static inline const PrecisionParams witness_prec_params = PrecisionParams{
      100u, 500u, Mg_dL{100u}, 240u, InsulinType::e_INSULIN_HUMALOG};
  static inline const PrecisionInput standard_input =
      PrecisionInput{Grams{60u},
                     Mg_dL{150u},
                     0u,
                     List<BolusEvent>::nil(),
                     ActivityState::e_ACTIVITY_NORMAL,
                     false,
                     FaultStatus::fault_none(),
                     std::optional<unsigned int>()};
  static inline const MmolPrecisionInput mmol_input =
      MmolPrecisionInput{Grams{60u},
                         83u,
                         0u,
                         List<BolusEvent>::nil(),
                         ActivityState::e_ACTIVITY_NORMAL,
                         false,
                         FaultStatus::fault_none(),
                         std::optional<unsigned int>()};
  static inline const PrecisionInput high_iob_input = PrecisionInput{
      Grams{0u},
      Mg_dL{150u},
      100u,
      List<BolusEvent>::cons(BolusEvent{120u, 85u},
                             List<BolusEvent>::cons(BolusEvent{100u, 80u},
                                                    List<BolusEvent>::nil())),
      ActivityState::e_ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_none(),
      std::optional<unsigned int>()};
  static inline const PrecisionInput tdd_exceeded_input =
      PrecisionInput{Grams{60u},
                     Mg_dL{150u},
                     2000u,
                     List<BolusEvent>::cons(
                         BolusEvent{500u, 1800u},
                         List<BolusEvent>::cons(
                             BolusEvent{500u, 1500u},
                             List<BolusEvent>::cons(BolusEvent{500u, 1000u},
                                                    List<BolusEvent>::nil()))),
                     ActivityState::e_ACTIVITY_NORMAL,
                     false,
                     FaultStatus::fault_none(),
                     std::make_optional<unsigned int>(70u)};
  static inline const PrecisionInput occlusion_input = PrecisionInput{
      Grams{60u},
      Mg_dL{150u},
      120u,
      List<BolusEvent>::cons(BolusEvent{40u, 100u}, List<BolusEvent>::nil()),
      ActivityState::e_ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_occlusion(),
      std::optional<unsigned int>()};
  static inline const PrecisionInput battery_low_input = PrecisionInput{
      Grams{60u},
      Mg_dL{150u},
      120u,
      List<BolusEvent>::cons(BolusEvent{40u, 100u}, List<BolusEvent>::nil()),
      ActivityState::e_ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_batterylow(),
      std::optional<unsigned int>()};
  static inline const PrecisionInput pediatric_capped_input =
      PrecisionInput{Grams{200u},
                     Mg_dL{400u},
                     0u,
                     List<BolusEvent>::nil(),
                     ActivityState::e_ACTIVITY_NORMAL,
                     false,
                     FaultStatus::fault_none(),
                     std::make_optional<unsigned int>(20u)};
  static inline const PumpState standard_pump =
      PumpState{2000u, 100u, 0u, false, 80u};
  static inline const PumpState low_battery_pump =
      PumpState{2000u, 100u, 0u, false, 4u};
  static inline const PrecisionResult standard_result =
      validated_precision_bolus(standard_input, witness_prec_params);
  static inline const PrecisionResult mmol_result =
      validated_mmol_bolus(mmol_input, witness_prec_params);
  static inline const PrecisionResult battery_low_result =
      validated_precision_bolus(battery_low_input, witness_prec_params);
  static inline const PrecisionResult pediatric_result =
      validated_precision_bolus(pediatric_capped_input, witness_prec_params);
  static inline const unsigned int standard_result_code =
      standard_result.precision_result_code();
  static inline const bool standard_modified =
      standard_result.result_modified();
  static inline const unsigned int standard_final_delivery_half =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDHALF, standard_result), 0u);
  static inline const bool standard_pump_accepts = pump_accepts_result(
      standard_pump, RoundingMode::e_ROUNDHALF, standard_result);
  static inline const unsigned int standard_reservoir_after =
      pump_reservoir_after_result(standard_pump, RoundingMode::e_ROUNDHALF,
                                  standard_result);
  static inline const unsigned int mmol_result_code =
      mmol_result.precision_result_code();
  static inline const unsigned int mmol_final_delivery_tenth =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDTENTH, mmol_result), 0u);
  static inline const unsigned int high_iob_error_code =
      validated_precision_bolus(high_iob_input, witness_prec_params)
          .precision_result_code();
  static inline const unsigned int tdd_error_code =
      validated_precision_bolus(tdd_exceeded_input, witness_prec_params)
          .precision_result_code();
  static inline const unsigned int occlusion_error_code =
      validated_precision_bolus(occlusion_input, witness_prec_params)
          .precision_result_code();
  static inline const unsigned int battery_low_result_code =
      battery_low_result.precision_result_code();
  static inline const bool battery_low_pump_denied = !(pump_accepts_result(
      low_battery_pump, RoundingMode::e_ROUNDHALF, battery_low_result));
  static inline const unsigned int pediatric_result_code =
      pediatric_result.precision_result_code();
  static inline const bool pediatric_modified =
      pediatric_result.result_modified();
  static inline const unsigned int pediatric_final_delivery =
      option_nat_default(
          final_delivery(RoundingMode::e_ROUNDTWENTIETH, pediatric_result), 0u);
  static inline const bool low_reservoir_blocks =
      FaultStatus::fault_lowreservoir(5u).fault_blocks_bolus();
  static inline const bool unknown_fault_blocks =
      FaultStatus::fault_unknown().fault_blocks_bolus();
};

#endif // INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
