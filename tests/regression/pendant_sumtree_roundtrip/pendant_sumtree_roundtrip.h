#ifndef INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
#define INCLUDED_PENDANT_SUMTREE_ROUNDTRIP

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil0 {};

  struct Cons0 {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil0, Cons0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil0 _v) : d_v_(_v) {}

  explicit List(Cons0 _v) : d_v_(std::move(_v)) {}

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
    if (std::holds_alternative<Nil0>(_sv.v())) {
      return List<t_A>(Nil0{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons0>(_sv.v());
      return List<t_A>(Cons0{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil0>(_other.v())) {
      d_v_ = Nil0{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons0>(_other.v());
      d_v_ =
          Cons0{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil0() { return List(Nil0{}); }

  __attribute__((pure)) static List<t_A> cons0(t_A a0, const List<t_A> &a1) {
    return List(Cons0{std::move(a0), std::make_unique<List<t_A>>(a1)});
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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bool forallb(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil0>(_sv.v())) {
      return true;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons0>(_sv.v());
      return (f(d_a0) && (*(d_a1)).forallb(f));
    }
  }

  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil0>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons0>(_sv.v());
      return f(d_a0, (*(d_a1)).template fold_right<T1>(f, a0));
    }
  }

  template <typename T1> __attribute__((pure)) List<T1> concat() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<List<T1>>::Nil0>(_sv.v())) {
      return List<T1>::nil0();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<T1>>::Cons0>(_sv.v());
      return d_a0.app((*(d_a1)).template concat<T1>());
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil0>(_sv.v())) {
      return List<T1>::nil0();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons0>(_sv.v());
      return List<T1>::cons0(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil0>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons0>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil0>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons0>(_sv.v());
      return List<t_A>::cons0(d_a0, (*(d_a1)).app(m));
    }
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{t_A(d_x)};
  }

  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> *operator->() { return this; }

  __attribute__((pure)) const Sig<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Sig<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  SigT(const SigT<t_A, t_P> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  SigT(SigT<t_A, t_P> &&_other) : d_v_(std::move(_other.d_v_)) {}

  SigT<t_A, t_P> &operator=(const SigT<t_A, t_P> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  SigT<t_A, t_P> &operator=(SigT<t_A, t_P> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) SigT<t_A, t_P> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x, d_a1] = std::get<ExistT>(_sv.v());
    return SigT<t_A, t_P>(ExistT{d_x, d_a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[d_x, d_a1] =
        std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    d_v_ = ExistT{t_A(d_x), t_P(d_a1)};
  }

  __attribute__((pure)) static SigT<t_A, t_P> existt(t_A x, t_P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) SigT<t_A, t_P> *operator->() { return this; }

  __attribute__((pure)) const SigT<t_A, t_P> *operator->() const {
    return this;
  }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = SigT<t_A, t_P>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct T0 {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_h;
    unsigned int d_n;
    std::unique_ptr<T0<t_A>> d_a2;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  T0() {}

  explicit T0(Nil _v) : d_v_(_v) {}

  explicit T0(Cons _v) : d_v_(std::move(_v)) {}

  T0(const T0<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  T0(T0<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  T0<t_A> &operator=(const T0<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  T0<t_A> &operator=(T0<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) T0<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return T0<t_A>(Nil{});
    } else {
      const auto &[d_h, d_n, d_a2] = std::get<Cons>(_sv.v());
      return T0<t_A>(Cons{
          d_h, d_n, d_a2 ? std::make_unique<T0<t_A>>(d_a2->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit T0(const T0<_U> &_other) {
    if (std::holds_alternative<typename T0<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_h, d_n, d_a2] =
          std::get<typename T0<_U>::Cons>(_other.v());
      d_v_ = Cons{t_A(d_h), d_n,
                  d_a2 ? std::make_unique<T0<t_A>>(*d_a2) : nullptr};
    }
  }

  constexpr static T0<t_A> nil() { return T0(Nil{}); }

  __attribute__((pure)) static T0<t_A> cons(t_A h, unsigned int n,
                                            const T0<t_A> &a2) {
    return T0(Cons{std::move(h), std::move(n), std::make_unique<T0<t_A>>(a2)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) T0<t_A> *operator->() { return this; }

  __attribute__((pure)) const T0<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = T0<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct T {
  // TYPES
  struct F1 {
    unsigned int d_n;
  };

  struct FS {
    unsigned int d_n;
    std::unique_ptr<T> d_a1;
  };

  using variant_t = std::variant<F1, FS>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  T() {}

  explicit T(F1 _v) : d_v_(std::move(_v)) {}

  explicit T(FS _v) : d_v_(std::move(_v)) {}

  T(const T &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  T(T &&_other) : d_v_(std::move(_other.d_v_)) {}

  T &operator=(const T &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  T &operator=(T &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) T clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<F1>(_sv.v())) {
      const auto &[d_n] = std::get<F1>(_sv.v());
      return T(F1{d_n});
    } else {
      const auto &[d_n, d_a1] = std::get<FS>(_sv.v());
      return T(FS{d_n, d_a1 ? std::make_unique<T>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static T f1(unsigned int n) {
    return T(F1{std::move(n)});
  }

  __attribute__((pure)) static T fs(unsigned int n, const T &a1) {
    return T(FS{std::move(n), std::make_unique<T>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) T *operator->() { return this; }

  __attribute__((pure)) const T *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = T(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Sig<unsigned int> to_nat(const unsigned int &) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename T::F1>(_sv.v())) {
      return Sig<unsigned int>::exist(0u);
    } else {
      const auto &[d_n, d_a1] = std::get<typename T::FS>(_sv.v());
      auto &&_sv0 = (*(d_a1)).to_nat(d_n);
      const auto &[d_x0] =
          std::get<typename Sig<unsigned int>::Exist>(_sv0.v());
      return Sig<unsigned int>::exist((d_x0 + 1));
    }
  }
};

struct Fin {
  static T of_nat_lt(const unsigned int &p, const unsigned int &n);
};

struct Vector {
  template <typename T1>
  __attribute__((pure)) static List<T1> to_list(const unsigned int &n,
                                                const T0<T1> &v);
};

struct Datatypes {
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::optional<T2>
  option_map(F0 &&f, const std::optional<T1> &o);
};

struct PendantSumtreeRoundtripCase {
  using digit = T;
  __attribute__((pure)) static unsigned int digit_to_nat(const T &d);
  __attribute__((pure)) static digit digit_of_nat(const unsigned int &n);
  static inline const digit digit0 = digit_of_nat(0u);
  static inline const digit digit1 = digit_of_nat(1u);
  static inline const digit digit2 = digit_of_nat(2u);
  static inline const digit digit3 = digit_of_nat(3u);
  static inline const digit digit4 = digit_of_nat(4u);
  static inline const digit digit5 = digit_of_nat(5u);
  static inline const digit digit6 = digit_of_nat(6u);
  static inline const digit digit7 = digit_of_nat(7u);
  static inline const digit digit9 = digit_of_nat(9u);
  __attribute__((pure)) static unsigned int value_digits(const unsigned int &_x,
                                                         const T0<T> &ds);
  __attribute__((pure)) static std::optional<T0<digit>>
  list_to_vector_opt(const unsigned int &n, const List<T> &xs);
  __attribute__((pure)) static List<List<digit>>
  encode_multi(unsigned int n, const List<T0<T>> &nums);
  __attribute__((pure)) static std::optional<List<T0<digit>>>
  decode_multi(unsigned int n, const List<List<T>> &segments);
  enum class Twist { e_TS, e_TZ };

  template <typename T1>
  static T1 Twist_rect(const T1 f, const T1 f0, const Twist t1) {
    switch (t1) {
    case Twist::e_TS: {
      return f;
    }
    case Twist::e_TZ: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Twist_rec(const T1 f, const T1 f0, const Twist t1) {
    switch (t1) {
    case Twist::e_TS: {
      return f;
    }
    case Twist::e_TZ: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }
  enum class Fiber { e_COTTON, e_CAMELID };

  template <typename T1>
  static T1 Fiber_rect(const T1 f, const T1 f0, const Fiber f1) {
    switch (f1) {
    case Fiber::e_COTTON: {
      return f;
    }
    case Fiber::e_CAMELID: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Fiber_rec(const T1 f, const T1 f0, const Fiber f1) {
    switch (f1) {
    case Fiber::e_COTTON: {
      return f;
    }
    case Fiber::e_CAMELID: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }
  enum class Color { e_WHITE, e_BROWN, e_RED, e_BLUE };

  template <typename T1>
  static T1 Color_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const Color c) {
    switch (c) {
    case Color::e_WHITE: {
      return f;
    }
    case Color::e_BROWN: {
      return f0;
    }
    case Color::e_RED: {
      return f1;
    }
    case Color::e_BLUE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Color_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const Color c) {
    switch (c) {
    case Color::e_WHITE: {
      return f;
    }
    case Color::e_BROWN: {
      return f0;
    }
    case Color::e_RED: {
      return f1;
    }
    case Color::e_BLUE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  struct CordMeta {
    Fiber cm_fiber;
    Color cm_color;
    Twist cm_spin;
    Twist cm_ply;

    __attribute__((pure)) CordMeta *operator->() { return this; }

    __attribute__((pure)) const CordMeta *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) CordMeta clone() const {
      return CordMeta{(*(this)).cm_fiber, (*(this)).cm_color, (*(this)).cm_spin,
                      (*(this)).cm_ply};
    }
  };

  struct CertifiedPendant {
    CordMeta cp_meta;
    T0<digit> cp_digits;

    __attribute__((pure)) CertifiedPendant *operator->() { return this; }

    __attribute__((pure)) const CertifiedPendant *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) CertifiedPendant clone() const {
      return CertifiedPendant{(*(this)).cp_meta.clone(),
                              (*(this)).cp_digits.clone()};
    }
  };

  __attribute__((pure)) static std::optional<T0<digit>>
  pendant_digits(const unsigned int &n, const CertifiedPendant &p);
  __attribute__((pure)) static std::optional<unsigned int>
  pendant_value(unsigned int n, const CertifiedPendant &p);
  using Ledger = List<SigT<unsigned int, CertifiedPendant>>;
  __attribute__((pure)) static List<std::optional<unsigned int>>
  ledger_values(const List<SigT<unsigned int, CertifiedPendant>> &l);

  struct PendantGroup {
    CertifiedPendant pg_top;
    List<CertifiedPendant> pg_pendants;

    __attribute__((pure)) PendantGroup *operator->() { return this; }

    __attribute__((pure)) const PendantGroup *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) PendantGroup clone() const {
      return PendantGroup{(*(this)).pg_top.clone(),
                          (*(this)).pg_pendants.clone()};
    }
  };

  __attribute__((pure)) static bool group_sums_validb(unsigned int n,
                                                      const PendantGroup &g);

  struct SumTree {
    // TYPES
    struct SumLeaf {
      CertifiedPendant d_a0;
    };

    struct SumNode {
      CertifiedPendant d_a0;
      std::unique_ptr<List<SumTree>> d_a1;
    };

    using variant_t = std::variant<SumLeaf, SumNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    SumTree() {}

    explicit SumTree(SumLeaf _v) : d_v_(std::move(_v)) {}

    explicit SumTree(SumNode _v) : d_v_(std::move(_v)) {}

    SumTree(const SumTree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    SumTree(SumTree &&_other) : d_v_(std::move(_other.d_v_)) {}

    SumTree &operator=(const SumTree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    SumTree &operator=(SumTree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) SumTree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<SumLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<SumLeaf>(_sv.v());
        return SumTree(SumLeaf{d_a0.clone()});
      } else {
        const auto &[d_a0, d_a1] = std::get<SumNode>(_sv.v());
        return SumTree(SumNode{
            d_a0.clone(),
            d_a1 ? std::make_unique<List<PendantSumtreeRoundtripCase::SumTree>>(
                       d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    constexpr static SumTree sumleaf(CertifiedPendant a0) {
      return SumTree(SumLeaf{std::move(a0)});
    }

    __attribute__((pure)) static SumTree sumnode(CertifiedPendant a0,
                                                 const List<SumTree> &a1) {
      return SumTree(
          SumNode{std::move(a0), std::make_unique<List<SumTree>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) SumTree *operator->() { return this; }

    __attribute__((pure)) const SumTree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = SumTree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, CertifiedPendant> F1,
            MapsTo<T1, CertifiedPendant, List<SumTree>> F2>
  static T1 SumTree_rect(const unsigned int &, F1 &&f, F2 &&f0,
                         const SumTree &s) {
    if (std::holds_alternative<typename SumTree::SumLeaf>(s.v())) {
      const auto &[d_a0] = std::get<typename SumTree::SumLeaf>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename SumTree::SumNode>(s.v());
      return f0(d_a0, *(d_a1));
    }
  }

  template <typename T1, MapsTo<T1, CertifiedPendant> F1,
            MapsTo<T1, CertifiedPendant, List<SumTree>> F2>
  static T1 SumTree_rec(const unsigned int &, F1 &&f, F2 &&f0,
                        const SumTree &s) {
    if (std::holds_alternative<typename SumTree::SumLeaf>(s.v())) {
      const auto &[d_a0] = std::get<typename SumTree::SumLeaf>(s.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename SumTree::SumNode>(s.v());
      return f0(d_a0, *(d_a1));
    }
  }

  __attribute__((pure)) static CertifiedPendant
  sumtree_top(const unsigned int &_x, const SumTree &st);
  __attribute__((pure)) static List<CertifiedPendant>
  sumtree_leaves(unsigned int n, const SumTree &st);
  __attribute__((pure)) static unsigned int sumtree_depth(unsigned int n,
                                                          const SumTree &st);
  __attribute__((pure)) static bool sumtree_validb_aux(unsigned int n,
                                                       const unsigned int &fuel,
                                                       const SumTree &st);
  __attribute__((pure)) static bool sumtree_validb(const unsigned int &n,
                                                   const SumTree &st);
  __attribute__((pure)) static std::optional<unsigned int>
  sumtree_leaf_total(unsigned int n, const SumTree &st);
  __attribute__((pure)) static bool nat_list_eqb(const List<unsigned int> &xs,
                                                 const List<unsigned int> &ys);
  __attribute__((pure)) static bool
  option_nat_eqb(const std::optional<unsigned int> &x,
                 const std::optional<unsigned int> &y);
  __attribute__((pure)) static bool
  option_nat_is_some(const std::optional<unsigned int> &x);
  __attribute__((pure)) static T0<digit> digit_vec1(T a);
  __attribute__((pure)) static T0<digit> digit_vec3(T a, T b, T c);
  static inline const CordMeta sample_meta_a =
      CordMeta{Fiber::e_COTTON, Color::e_BROWN, Twist::e_TS, Twist::e_TZ};
  static inline const CordMeta sample_meta_b =
      CordMeta{Fiber::e_CAMELID, Color::e_RED, Twist::e_TZ, Twist::e_TS};
  static inline const CordMeta sample_meta_c =
      CordMeta{Fiber::e_COTTON, Color::e_BLUE, Twist::e_TS, Twist::e_TS};
  static inline const T0<digit> digits_731 = digit_vec3(digit1, digit3, digit7);
  static inline const T0<digit> digits_462 = digit_vec3(digit2, digit6, digit4);
  static inline const T0<digit> digits_269 = digit_vec3(digit9, digit6, digit2);
  static inline const T0<digit> digits_200 = digit_vec3(digit0, digit0, digit2);
  static inline const T0<digit> digits_069 = digit_vec3(digit9, digit6, digit0);
  static inline const T0<digit> digits_5 = digit_vec1(digit5);
  static inline const CertifiedPendant pendant_731 =
      CertifiedPendant{sample_meta_a, digits_731};
  static inline const CertifiedPendant pendant_462 =
      CertifiedPendant{sample_meta_b, digits_462};
  static inline const CertifiedPendant pendant_269 =
      CertifiedPendant{sample_meta_c, digits_269};
  static inline const CertifiedPendant pendant_200 =
      CertifiedPendant{sample_meta_b, digits_200};
  static inline const CertifiedPendant pendant_069 =
      CertifiedPendant{sample_meta_c, digits_069};
  static inline const CertifiedPendant pendant_5 =
      CertifiedPendant{sample_meta_a, digits_5};
  static inline const List<T0<digit>> sample_multi_digits = List<T0<T>>::cons0(
      digits_731,
      List<T0<T>>::cons0(digits_462,
                         List<T0<T>>::cons0(digits_269, List<T0<T>>::nil0())));
  static inline const bool sample_multi_roundtrip_ok = []() -> bool {
    auto _cs = decode_multi(3u, encode_multi(3u, sample_multi_digits));
    if (_cs.has_value()) {
      const List<T0<T>> &decoded = *_cs;
      return nat_list_eqb(
          decoded.template map<unsigned int>([](T0<digit> _x0) -> unsigned int {
            return value_digits(3u, _x0);
          }),
          List<unsigned int>::cons0(
              731u, List<unsigned int>::cons0(
                        462u, List<unsigned int>::cons0(
                                  269u, List<unsigned int>::nil0()))));
    } else {
      return false;
    }
  }();
  static inline const PendantGroup sample_group = PendantGroup{
      pendant_731,
      List<CertifiedPendant>::cons0(
          pendant_462, List<CertifiedPendant>::cons0(
                           pendant_269, List<CertifiedPendant>::nil0()))};
  static inline const SumTree sample_subtree = SumTree::sumnode(
      pendant_269,
      List<SumTree>::cons0(SumTree::sumleaf(pendant_200),
                           List<SumTree>::cons0(SumTree::sumleaf(pendant_069),
                                                List<SumTree>::nil0())));
  static inline const SumTree sample_tree = SumTree::sumnode(
      pendant_731,
      List<SumTree>::cons0(
          SumTree::sumleaf(pendant_462),
          List<SumTree>::cons0(sample_subtree, List<SumTree>::nil0())));
  static inline const Ledger sample_ledger =
      List<SigT<unsigned int, CertifiedPendant>>::cons0(
          SigT<unsigned int, CertifiedPendant>::existt(3u, pendant_731),
          List<SigT<unsigned int, CertifiedPendant>>::cons0(
              SigT<unsigned int, CertifiedPendant>::existt(3u, pendant_462),
              List<SigT<unsigned int, CertifiedPendant>>::cons0(
                  SigT<unsigned int, CertifiedPendant>::existt(1u, pendant_5),
                  List<SigT<unsigned int, CertifiedPendant>>::nil0())));
  static inline const bool sample_group_valid =
      group_sums_validb(3u, sample_group);
  static inline const bool sample_subtree_valid =
      sumtree_validb(3u, sample_subtree);
  static inline const bool sample_tree_valid = sumtree_validb(3u, sample_tree);
  static inline const bool sample_leaf_total_matches_root = option_nat_eqb(
      sumtree_leaf_total(3u, sample_tree), pendant_value(3u, pendant_731));
  static inline const unsigned int sample_tree_depth =
      sumtree_depth(3u, sample_tree);
  static inline const unsigned int sample_ledger_entry_count =
      ledger_values(sample_ledger).length();
  static inline const bool sample_ledger_all_present =
      ledger_values(sample_ledger).forallb(option_nat_is_some);
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
__attribute__((pure)) std::optional<T2>
Datatypes::option_map(F0 &&f, const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &a = *o;
    return std::make_optional<T2>(f(a));
  } else {
    return std::optional<T2>();
  }
}

template <typename T1>
__attribute__((pure)) List<T1> Vector::to_list(const unsigned int &n,
                                               const T0<T1> &v) {
  std::function<List<T1>(unsigned int, T0<T1>, List<T1>)> fold_right_fix;
  fold_right_fix = [&](unsigned int, T0<T1> v0, List<T1> b) -> List<T1> {
    if (std::holds_alternative<typename T0<T1>::Nil>(v0.v())) {
      return b;
    } else {
      const auto &[d_h, d_n, d_a2] = std::get<typename T0<T1>::Cons>(v0.v());
      return List<T1>::cons0(d_h, fold_right_fix(d_n, *(d_a2), b));
    }
  };
  return fold_right_fix(n, v, List<T1>::nil0());
}

#endif // INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
