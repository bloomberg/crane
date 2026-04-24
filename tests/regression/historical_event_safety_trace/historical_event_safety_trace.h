#ifndef INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
#define INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

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

struct HistoricalEventSafetyTraceCase {
  struct State {
    unsigned int reservoir_level_cm;
    unsigned int downstream_stage_cm;
    unsigned int gate_open_pct;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }
  };

  struct PlantConfig {
    unsigned int max_reservoir_cm;
    unsigned int max_downstream_cm;
    unsigned int gate_capacity_cm;
    unsigned int forecast_error_pct;
    unsigned int gate_slew_pct;
    unsigned int max_stage_rise_cm;
    unsigned int reservoir_area_min_cm2;
    unsigned int reservoir_area_max_cm2;
    std::function<unsigned int(unsigned int)> reservoir_area_curve_cm2;
    unsigned int design_head_cm;
    unsigned int timestep_s;

    __attribute__((pure)) PlantConfig *operator->() { return this; }

    __attribute__((pure)) const PlantConfig *operator->() const { return this; }
  };

  __attribute__((pure)) static bool is_safe_bool(const PlantConfig &pconf,
                                                 const State &s);

  struct InflowRecord {
    unsigned int ir_timestep;
    unsigned int ir_inflow_cm;

    __attribute__((pure)) InflowRecord *operator->() { return this; }

    __attribute__((pure)) const InflowRecord *operator->() const {
      return this;
    }
  };

  using HistoricalEvent = List<InflowRecord>;
  __attribute__((pure)) static unsigned int
  event_to_inflow(const List<InflowRecord> &event, unsigned int default_inflow,
                  const unsigned int &t);

  struct TestResult {
    unsigned int tr_event_name;
    bool tr_initial_safe;
    bool tr_final_safe;
    unsigned int tr_max_level;
    unsigned int tr_max_stage;

    __attribute__((pure)) TestResult *operator->() { return this; }

    __attribute__((pure)) const TestResult *operator->() const { return this; }
  };

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, State, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  __attribute__((pure)) static State
  step_hist(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn, const PlantConfig &pconf,
            const State &s, const unsigned int &t) {
    unsigned int out =
        std::min((100u ? (pconf.gate_capacity_cm * ctrl(s, t)) / 100u : 0),
                 (s.reservoir_level_cm + inflow(t)));
    unsigned int new_level =
        ((((s.reservoir_level_cm + inflow(t)) - out) >
                  (s.reservoir_level_cm + inflow(t))
              ? 0
              : ((s.reservoir_level_cm + inflow(t)) - out)));
    unsigned int new_stage = stage_fn(out);
    return State{new_level, new_stage, ctrl(s, t)};
  }

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, State, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  __attribute__((
      pure)) static std::pair<std::pair<State, unsigned int>, unsigned int>
  simulate_with_max(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                    const PlantConfig &pconf, const unsigned int &horizon,
                    State s, unsigned int max_level, unsigned int max_stage) {
    if (horizon <= 0) {
      return std::make_pair(std::make_pair(s, max_level), max_stage);
    } else {
      unsigned int k = horizon - 1;
      State s_ = step_hist(inflow, ctrl, stage_fn, pconf, s, k);
      return simulate_with_max(inflow, ctrl, stage_fn, pconf, k, s_,
                               std::max(max_level, s_.reservoir_level_cm),
                               std::max(max_stage, s_.downstream_stage_cm));
    }
  }

  template <MapsTo<unsigned int, State, unsigned int> F3,
            MapsTo<unsigned int, unsigned int> F4>
  __attribute__((pure)) static TestResult
  run_historical_test(const PlantConfig &pconf, List<InflowRecord> event,
                      unsigned int default_inflow, F3 &&ctrl, F4 &&stage_fn,
                      const State &initial_state, const unsigned int &horizon,
                      unsigned int event_id) {
    std::function<unsigned int(unsigned int)> inflow =
        [=](unsigned int _x0) mutable -> unsigned int {
      return event_to_inflow(event, default_inflow, _x0);
    };
    bool initial_safe = is_safe_bool(pconf, initial_state);
    auto _cs = simulate_with_max(inflow, ctrl, stage_fn, pconf, horizon,
                                 initial_state, 0u, 0u);
    const std::pair<State, unsigned int> &p = _cs.first;
    const unsigned int &max_stg = _cs.second;
    const State &final_state = p.first;
    const unsigned int &max_lev = p.second;
    bool final_safe = is_safe_bool(pconf, final_state);
    return TestResult{event_id, initial_safe, final_safe, max_lev, max_stg};
  }

  __attribute__((pure)) static bool test_passes(const TestResult &result);
  __attribute__((pure)) static bool
  all_tests_pass(const List<TestResult> &results);
  using RatingTable = List<std::pair<unsigned int, unsigned int>>;
  __attribute__((pure)) static unsigned int
  stage_from_table(const List<std::pair<unsigned int, unsigned int>> &tbl,
                   unsigned int base_stage, const unsigned int &out);

  struct MonotoneRatingTable {
    RatingTable mrt_table;

    __attribute__((pure)) MonotoneRatingTable *operator->() { return this; }

    __attribute__((pure)) const MonotoneRatingTable *operator->() const {
      return this;
    }
  };

  static inline const HistoricalEvent flood_1983_inflows =
      List<InflowRecord>::cons(
          InflowRecord{0u, 50u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 75u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 100u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 150u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 200u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 250u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 300u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 250u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 200u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 150u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent flood_2011_inflows =
      List<InflowRecord>::cons(
          InflowRecord{0u, 100u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 150u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 200u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 300u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 400u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 350u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 300u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 250u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 200u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 150u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent dual_peak_scenario =
      List<InflowRecord>::cons(
          InflowRecord{0u, 30u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 60u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 120u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 200u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 300u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 380u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 420u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 400u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 350u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 280u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const PlantConfig hist_witness_plant =
      PlantConfig{500u, 500u, 500u,
                  1u,   5u,   10u,
                  100u, 100u, [](const unsigned int &) {
return 100u; },
                  100u, 1u};
  __attribute__((pure)) static unsigned int
  hist_witness_stage(const unsigned int &out);
  __attribute__((pure)) static unsigned int
  hist_witness_ctrl(const State &s, const unsigned int &_x);
  static inline const State hist_witness_initial = State{50u, 0u, 0u};
  static inline const TestResult hist_test_1983 = run_historical_test(
      hist_witness_plant, flood_1983_inflows, 0u, hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, 10u, 1983u);
  static inline const TestResult hist_test_2011 = run_historical_test(
      hist_witness_plant, flood_2011_inflows, 0u, hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, 10u, 2011u);
  static inline const PlantConfig hoover_dam_config =
      PlantConfig{2200u, 100u,  500u,
                  15u,   5u,    10u,
                  1000u, 1000u, [](const unsigned int &) {
return 1000u; },
                  200u,  60u};
  static inline const State hoover_initial_state = State{1500u, 20u, 0u};
  __attribute__((pure)) static unsigned int
  hoover_controller(const State &s, const unsigned int &_x);
  static inline const MonotoneRatingTable hoover_rating_table =
      MonotoneRatingTable{List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(100u, 30u),
          List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(200u, 45u),
              List<std::pair<unsigned int, unsigned int>>::cons(
                  std::make_pair(300u, 60u),
                  List<std::pair<unsigned int, unsigned int>>::cons(
                      std::make_pair(400u, 75u),
                      List<std::pair<unsigned int, unsigned int>>::cons(
                          std::make_pair(500u, 90u),
                          List<std::pair<unsigned int,
                                         unsigned int>>::nil())))))};
  __attribute__((pure)) static unsigned int
  hoover_stage_from_rating(const unsigned int &out);
  static inline const TestResult hoover_test = run_historical_test(
      hoover_dam_config, dual_peak_scenario, 0u, hoover_controller,
      hoover_stage_from_rating, hoover_initial_state, 10u, 9001u);

  struct HistoricalScenarioBundle {
    PlantConfig hsb_hist_plant;
    MonotoneRatingTable hsb_hist_table;
    State hsb_hist_initial;
    TestResult hsb_test_1983;
    TestResult hsb_test_2011;
    PlantConfig hsb_hoover_plant;
    TestResult hsb_hoover_test;

    __attribute__((pure)) HistoricalScenarioBundle *operator->() {
      return this;
    }

    __attribute__((pure)) const HistoricalScenarioBundle *operator->() const {
      return this;
    }
  };

  static inline const HistoricalScenarioBundle historical_bundle =
      HistoricalScenarioBundle{hist_witness_plant,   hoover_rating_table,
                               hist_witness_initial, hist_test_1983,
                               hist_test_2011,       hoover_dam_config,
                               hoover_test};
  __attribute__((pure)) static unsigned int
  historical_lookup_1983(const unsigned int &t);
  __attribute__((pure)) static unsigned int
  historical_lookup_2011(const unsigned int &t);
  __attribute__((pure)) static bool
  witness_test_initial_safe_at(const unsigned int &h);
  __attribute__((pure)) static unsigned int
  witness_test_peak_level_at(const unsigned int &h);
  __attribute__((pure)) static unsigned int
  hoover_controller_sample(unsigned int level);
  __attribute__((pure)) static unsigned int
  hoover_stage_sample(const unsigned int &_x0);
  static inline const unsigned int sample_bundle_test_count =
      List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil())))
          .length();
  static inline const bool sample_bundle_initial_safe =
      historical_bundle.hsb_test_1983.tr_initial_safe;
  static inline const unsigned int sample_bundle_hist_2011_id =
      historical_bundle.hsb_test_2011.tr_event_name;
  static inline const bool sample_all_tests_pass =
      all_tests_pass(List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil()))));
};

#endif // INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
