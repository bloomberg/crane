#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
      return Uint(D0{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D1>(_sv.v())) {
      const auto &[d_a0] = std::get<D1>(_sv.v());
      return Uint(D1{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D2>(_sv.v())) {
      const auto &[d_a0] = std::get<D2>(_sv.v());
      return Uint(D2{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D3>(_sv.v())) {
      const auto &[d_a0] = std::get<D3>(_sv.v());
      return Uint(D3{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D4>(_sv.v())) {
      const auto &[d_a0] = std::get<D4>(_sv.v());
      return Uint(D4{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D5>(_sv.v())) {
      const auto &[d_a0] = std::get<D5>(_sv.v());
      return Uint(D5{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D6>(_sv.v())) {
      const auto &[d_a0] = std::get<D6>(_sv.v());
      return Uint(D6{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D7>(_sv.v())) {
      const auto &[d_a0] = std::get<D7>(_sv.v());
      return Uint(D7{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else if (std::holds_alternative<D8>(_sv.v())) {
      const auto &[d_a0] = std::get<D8>(_sv.v());
      return Uint(D8{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    } else {
      const auto &[d_a0] = std::get<D9>(_sv.v());
      return Uint(D9{clone_as_value<std::unique_ptr<Uint>>(d_a0)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint nil() { return Uint(Nil{}); }

  __attribute__((pure)) static Uint d0(const Uint &a0) {
    return Uint(D0{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d1(const Uint &a0) {
    return Uint(D1{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d2(const Uint &a0) {
    return Uint(D2{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d3(const Uint &a0) {
    return Uint(D3{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d4(const Uint &a0) {
    return Uint(D4{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d5(const Uint &a0) {
    return Uint(D5{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d6(const Uint &a0) {
    return Uint(D6{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d7(const Uint &a0) {
    return Uint(D7{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d8(const Uint &a0) {
    return Uint(D8{std::make_unique<Uint>(a0.clone())});
  }

  __attribute__((pure)) static Uint d9(const Uint &a0) {
    return Uint(D9{std::make_unique<Uint>(a0.clone())});
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
      return Uint0(D10{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D11>(_sv.v())) {
      const auto &[d_a0] = std::get<D11>(_sv.v());
      return Uint0(D11{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D12>(_sv.v())) {
      const auto &[d_a0] = std::get<D12>(_sv.v());
      return Uint0(D12{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D13>(_sv.v())) {
      const auto &[d_a0] = std::get<D13>(_sv.v());
      return Uint0(D13{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D14>(_sv.v())) {
      const auto &[d_a0] = std::get<D14>(_sv.v());
      return Uint0(D14{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D15>(_sv.v())) {
      const auto &[d_a0] = std::get<D15>(_sv.v());
      return Uint0(D15{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D16>(_sv.v())) {
      const auto &[d_a0] = std::get<D16>(_sv.v());
      return Uint0(D16{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D17>(_sv.v())) {
      const auto &[d_a0] = std::get<D17>(_sv.v());
      return Uint0(D17{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D18>(_sv.v())) {
      const auto &[d_a0] = std::get<D18>(_sv.v());
      return Uint0(D18{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<D19>(_sv.v())) {
      const auto &[d_a0] = std::get<D19>(_sv.v());
      return Uint0(D19{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<Da>(_sv.v())) {
      const auto &[d_a0] = std::get<Da>(_sv.v());
      return Uint0(Da{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<Db>(_sv.v())) {
      const auto &[d_a0] = std::get<Db>(_sv.v());
      return Uint0(Db{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<Dc>(_sv.v())) {
      const auto &[d_a0] = std::get<Dc>(_sv.v());
      return Uint0(Dc{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<Dd>(_sv.v())) {
      const auto &[d_a0] = std::get<Dd>(_sv.v());
      return Uint0(Dd{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else if (std::holds_alternative<De>(_sv.v())) {
      const auto &[d_a0] = std::get<De>(_sv.v());
      return Uint0(De{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    } else {
      const auto &[d_a0] = std::get<Df>(_sv.v());
      return Uint0(Df{clone_as_value<std::unique_ptr<Uint0>>(d_a0)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Uint0 nil0() { return Uint0(Nil0{}); }

  __attribute__((pure)) static Uint0 d10(const Uint0 &a0) {
    return Uint0(D10{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d11(const Uint0 &a0) {
    return Uint0(D11{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d12(const Uint0 &a0) {
    return Uint0(D12{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d13(const Uint0 &a0) {
    return Uint0(D13{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d14(const Uint0 &a0) {
    return Uint0(D14{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d15(const Uint0 &a0) {
    return Uint0(D15{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d16(const Uint0 &a0) {
    return Uint0(D16{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d17(const Uint0 &a0) {
    return Uint0(D17{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d18(const Uint0 &a0) {
    return Uint0(D18{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 d19(const Uint0 &a0) {
    return Uint0(D19{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 da(const Uint0 &a0) {
    return Uint0(Da{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 db(const Uint0 &a0) {
    return Uint0(Db{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 dc(const Uint0 &a0) {
    return Uint0(Dc{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 dd(const Uint0 &a0) {
    return Uint0(Dd{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 de(const Uint0 &a0) {
    return Uint0(De{std::make_unique<Uint0>(a0.clone())});
  }

  __attribute__((pure)) static Uint0 df(const Uint0 &a0) {
    return Uint0(Df{std::make_unique<Uint0>(a0.clone())});
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
      return Uint1(UIntDecimal{clone_as_value<Uint>(d_u)});
    } else {
      const auto &[d_u] = std::get<UIntHexadecimal>(_sv.v());
      return Uint1(UIntHexadecimal{clone_as_value<Uint0>(d_u)});
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
        return tree<t_A>(
            Node{clone_as_value<std::unique_ptr<tree<t_A>>>(d_a0),
                 clone_as_value<t_A>(d_a1),
                 clone_as_value<std::unique_ptr<tree<t_A>>>(d_a2)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) tree<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree<_CloneT0>(typename tree<_CloneT0>::Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree<_CloneT0>(typename tree<_CloneT0>::Node{
            clone_as_value<std::unique_ptr<tree<_CloneT0>>>(d_a0),
            clone_as_value<_CloneT0>(d_a1),
            clone_as_value<std::unique_ptr<tree<_CloneT0>>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A> node(const tree<t_A> &a0, t_A a1,
                                                const tree<t_A> &a2) {
      return tree(Node{std::make_unique<tree<t_A>>(a0.clone()), std::move(a1),
                       std::make_unique<tree<t_A>>(a2.clone())});
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
    struct _Enter {
      const tree<T1> t;
    };

    struct _Call1 {
      tree<T1> _s0;
      tree<T1> _s1;
      T1 _s2;
      tree<T1> _s3;
    };

    struct _Call2 {
      T2 _s0;
      tree<T1> _s1;
      T1 _s2;
      tree<T1> _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Call1{*(d_a0), *(d_a2), d_a1, *(d_a0)});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, tree<T1>, T2, T1, tree<T1>, T2> F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const tree<T1> &t) {
    struct _Enter {
      const tree<T1> t;
    };

    struct _Call1 {
      tree<T1> _s0;
      tree<T1> _s1;
      T1 _s2;
      tree<T1> _s3;
    };

    struct _Call2 {
      T2 _s0;
      tree<T1> _s1;
      T1 _s2;
      tree<T1> _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Call1{*(d_a0), *(d_a2), d_a1, *(d_a0)});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  __attribute__((pure)) static tree<unsigned int> depth_tree(unsigned int n);

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static tree<T2> tree_map(F0 &&f, const tree<T1> &t) {
    struct _Enter {
      const tree<T1> t;
    };

    struct _Call1 {
      tree<T1> _s0;
      T2 _s1;
    };

    struct _Call2 {
      tree<T2> _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    tree<T2> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Call1{*(d_a0), f(d_a1)});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result, _f._s1});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = tree<T2>::node(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T2, T1, T2> F1>
  static T2 tree_fold(const T2 base, F1 &&f, const tree<T1> &t) {
    struct _Enter {
      const tree<T1> t;
    };

    struct _Call1 {
      tree<T1> _s0;
      T1 _s1;
    };

    struct _Call2 {
      T2 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = base;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Call1{*(d_a0), d_a1});
          _stack.emplace_back(_Enter{*(d_a2)});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result, _f._s1});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = f(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  __attribute__((pure)) static tree<T3>
  tree_zip_with(F0 &&f, const tree<T1> &t1, const tree<T2> &t2) {
    struct _Enter {
      const tree<T2> t2;
      const tree<T1> t1;
    };

    struct _Call1 {
      tree<T2> _s0;
      tree<T1> _s1;
      T3 _s2;
    };

    struct _Call2 {
      tree<T3> _s0;
      T3 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    tree<T3> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t2, t1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T2> t2 = _f.t2;
        const tree<T1> t1 = _f.t1;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t1.v())) {
          _result = tree<T3>::leaf();
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t1.v());
          if (std::holds_alternative<typename tree<T2>::Leaf>(t2.v())) {
            _result = tree<T3>::leaf();
          } else {
            const auto &[d_a00, d_a10, d_a20] =
                std::get<typename tree<T2>::Node>(t2.v());
            _stack.emplace_back(_Call1{*(d_a00), *(d_a0), f(d_a1, d_a10)});
            _stack.emplace_back(_Enter{*(d_a20), *(d_a2)});
          }
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        _stack.emplace_back(_Call2{_result, _f._s2});
        _stack.emplace_back(_Enter{_f._s0, _f._s1});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        _result = tree<T3>::node(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, tree<T2>>
  tree_map_accum(F0 &&f, const T3 acc, const tree<T1> &t) {
    struct _Enter {
      const tree<T1> t;
      const T3 acc;
    };

    struct _Call1 {
      T1 _s0;
      std::unique_ptr<tree<T1>> _s1;
      F0 _s2;
    };

    struct _Call2 {
      tree<T2> _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::pair<T3, tree<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{t, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> t = _f.t;
        const T3 acc = _f.acc;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::make_pair(acc, tree<T2>::leaf());
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Call1{d_a1, d_a2, f});
          _stack.emplace_back(_Enter{*(d_a0), acc});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a1 = _f._s0;
        std::unique_ptr<tree<T1>> d_a2 = _f._s1;
        F0 f = _f._s2;
        const T3 &acc1 = _result.first;
        const tree<T2> &l_ = _result.second;
        auto _cs1 = f(acc1, d_a1);
        const T3 &acc2 = _cs1.first;
        const T2 &x_ = _cs1.second;
        _stack.emplace_back(_Call2{l_, x_});
        _stack.emplace_back(_Enter{*(d_a2), acc2});
      } else {
        auto _f = std::move(std::get<_Call2>(_frame));
        tree<T2> l_ = _f._s0;
        T2 x_ = _f._s1;
        const T3 &acc3 = _result.first;
        const tree<T2> &r_ = _result.second;
        _result = std::make_pair(acc3, tree<T2>::node(l_, x_, r_));
      }
    }
    return _result;
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
