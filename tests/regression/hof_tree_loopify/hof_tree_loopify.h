#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

  __attribute__((pure)) Uint &operator=(const Uint &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Uint &operator=(Uint &&_other) {
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

  __attribute__((pure)) static Uint d0(const Uint &a0) {
    return Uint(D0{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d1(const Uint &a0) {
    return Uint(D1{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d2(const Uint &a0) {
    return Uint(D2{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d3(const Uint &a0) {
    return Uint(D3{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d4(const Uint &a0) {
    return Uint(D4{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d5(const Uint &a0) {
    return Uint(D5{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d6(const Uint &a0) {
    return Uint(D6{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d7(const Uint &a0) {
    return Uint(D7{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d8(const Uint &a0) {
    return Uint(D8{std::make_unique<Uint>(a0)});
  }

  __attribute__((pure)) static Uint d9(const Uint &a0) {
    return Uint(D9{std::make_unique<Uint>(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Uint *operator->() { return this; }

  __attribute__((pure)) const Uint *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Uint(); }

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

  __attribute__((pure)) Uint0 &operator=(const Uint0 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Uint0 &operator=(Uint0 &&_other) {
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

  __attribute__((pure)) static Uint0 d10(const Uint0 &a0) {
    return Uint0(D10{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d11(const Uint0 &a0) {
    return Uint0(D11{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d12(const Uint0 &a0) {
    return Uint0(D12{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d13(const Uint0 &a0) {
    return Uint0(D13{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d14(const Uint0 &a0) {
    return Uint0(D14{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d15(const Uint0 &a0) {
    return Uint0(D15{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d16(const Uint0 &a0) {
    return Uint0(D16{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d17(const Uint0 &a0) {
    return Uint0(D17{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d18(const Uint0 &a0) {
    return Uint0(D18{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 d19(const Uint0 &a0) {
    return Uint0(D19{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 da(const Uint0 &a0) {
    return Uint0(Da{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 db(const Uint0 &a0) {
    return Uint0(Db{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 dc(const Uint0 &a0) {
    return Uint0(Dc{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 dd(const Uint0 &a0) {
    return Uint0(Dd{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 de(const Uint0 &a0) {
    return Uint0(De{std::make_unique<Uint0>(a0)});
  }

  __attribute__((pure)) static Uint0 df(const Uint0 &a0) {
    return Uint0(Df{std::make_unique<Uint0>(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Uint0 *operator->() { return this; }

  __attribute__((pure)) const Uint0 *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Uint0(); }

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

  __attribute__((pure)) Uint1 &operator=(const Uint1 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Uint1 &operator=(Uint1 &&_other) {
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
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Uint1 *operator->() { return this; }

  __attribute__((pure)) const Uint1 *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Uint1(); }

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

struct HofTreeLoopify {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::unique_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree<t_A> &operator=(tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree<t_A>(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        t_A __c1;
        if constexpr (
            requires { d_a1 ? 0 : 0; } && requires { *d_a1; } &&
            requires { d_a1->clone(); } && requires { d_a1.get(); }) {
          using _E = std::remove_cvref_t<decltype(*d_a1)>;
          __c1 = d_a1 ? std::make_unique<_E>(d_a1->clone()) : nullptr;
        } else if constexpr (requires { d_a1.clone(); }) {
          __c1 = d_a1.clone();
        } else {
          __c1 = d_a1;
        }
        return tree<t_A>(Node{
            d_a0 ? std::make_unique<HofTreeLoopify::tree<t_A>>(d_a0->clone())
                 : nullptr,
            std::move(__c1),
            d_a2 ? std::make_unique<HofTreeLoopify::tree<t_A>>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        d_v_ = Leaf{};
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        d_v_ = Node{d_a0 ? std::make_unique<tree<t_A>>(*d_a0) : nullptr,
                    [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
                      if constexpr (
                          requires { *__v; } &&
                          !requires { std::declval<_DstT>().get(); })
                        return _DstT(*__v);
                      else if constexpr (
                          !requires { *__v; } &&
                          requires { std::declval<_DstT>().get(); }) {
                        using _E = std::remove_pointer_t<
                            decltype(std::declval<_DstT>().get())>;
                        return std::make_unique<_E>(std::move(__v));
                      } else
                        return _DstT(__v);
                    }(d_a1),
                    d_a2 ? std::make_unique<tree<t_A>>(*d_a2) : nullptr};
      }
    }

    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A> node(const tree<t_A> &a0, t_A a1,
                                                const tree<t_A> &a2) {
      return tree(Node{std::make_unique<tree<t_A>>(a0), std::move(a1),
                       std::make_unique<tree<t_A>>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> *operator->() { return this; }

    __attribute__((pure)) const tree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, tree<T1>, T2, T1, tree<T1>, T2> F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1, T2>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1, T2>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, tree<T1>, T2, T1, tree<T1>, T2> F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1, T2>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1, T2>(f, f0, *(d_a2)));
    }
  }

  __attribute__((pure)) static tree<unsigned int> depth_tree(unsigned int n);

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static tree<T2> tree_map(F0 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return tree<T2>::node(tree_map<T1, T2>(f, *(d_a0)), f(d_a1),
                            tree_map<T1, T2>(f, *(d_a2)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T2, T1, T2> F1>
  static T2 tree_fold(const T2 base, F1 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return base;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      return f(tree_fold<T1, T2>(base, f, *(d_a0)), d_a1,
               tree_fold<T1, T2>(base, f, *(d_a2)));
    }
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  __attribute__((pure)) static tree<T3>
  tree_zip_with(F0 &&f, const tree<T1> &t1, const tree<T2> &t2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t1.v())) {
      return tree<T3>::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename tree<T1>::Node>(t1.v());
      if (std::holds_alternative<typename tree<T2>::Leaf>(t2.v())) {
        return tree<T3>::leaf();
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename tree<T2>::Node>(t2.v());
        return tree<T3>::node(tree_zip_with<T1, T2, T3>(f, *(d_a0), *(d_a00)),
                              f(d_a1, d_a10),
                              tree_zip_with<T1, T2, T3>(f, *(d_a2), *(d_a20)));
      }
    }
  }

  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, tree<T2>>
  tree_map_accum(F0 &&f, const T3 acc, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return std::make_pair(acc, tree<T2>::leaf());
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree<T1>::Node>(t.v());
      auto _cs = tree_map_accum<T1, T2, T3>(f, acc, *(d_a0));
      const T3 &acc1 = _cs.first;
      const tree<T2> &l_ = _cs.second;
      auto _cs1 = f(acc1, d_a1);
      const T3 &acc2 = _cs1.first;
      const T2 &x_ = _cs1.second;
      auto _cs2 = tree_map_accum<T1, T2, T3>(f, acc2, *(d_a2));
      const T3 &acc3 = _cs2.first;
      const tree<T2> &r_ = _cs2.second;
      return std::make_pair(acc3, tree<T2>::node(l_, x_, r_));
    }
  }

  static inline const tree<unsigned int> small_tree = tree<unsigned int>::node(
      tree<unsigned int>::node(
          tree<unsigned int>::node(tree<unsigned int>::leaf(), 1u,
                                   tree<unsigned int>::leaf()),
          2u,
          tree<unsigned int>::node(tree<unsigned int>::leaf(), 3u,
                                   tree<unsigned int>::leaf())),
      4u,
      tree<unsigned int>::node(
          tree<unsigned int>::node(tree<unsigned int>::leaf(), 5u,
                                   tree<unsigned int>::leaf()),
          6u,
          tree<unsigned int>::node(tree<unsigned int>::leaf(), 7u,
                                   tree<unsigned int>::leaf())));
  static inline const tree<unsigned int> mapped =
      tree_map<unsigned int, unsigned int>(
          [](const unsigned int &x) { return (x * 2u); }, small_tree);
  static inline const unsigned int folded =
      tree_fold<unsigned int, unsigned int>(
          0u,
          [](const unsigned int &l, const unsigned int &x,
             const unsigned int &r) { return ((l + x) + r); },
          small_tree);
  static inline const tree<unsigned int> zipped =
      tree_zip_with<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          small_tree, small_tree);
  static inline const std::pair<unsigned int, tree<unsigned int>> accum =
      tree_map_accum<unsigned int, unsigned int, unsigned int>(
          [](unsigned int s, const unsigned int &x) {
            return std::make_pair((s + x), s);
          },
          0u, small_tree);
  static inline const tree<unsigned int> deep = depth_tree(50000u);
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
