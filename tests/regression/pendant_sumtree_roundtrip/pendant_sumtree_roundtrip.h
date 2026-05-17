#ifndef INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
#define INCLUDED_PENDANT_SUMTREE_ROUNDTRIP

#include <algorithm>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil0 {};

  struct Cons0 {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil0, Cons0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil0 _v) : v_(_v) {}

  explicit List(Cons0 _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil0>(_src->v())) {
        _dst->v_ = Nil0{};
      } else {
        const auto &_alt = std::get<Cons0>(_src->v());
        _dst->v_ =
            Cons0{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons0>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil0>(_other.v())) {
      this->v_ = Nil0{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons0>(_other.v());
      this->v_ = Cons0{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil0() { return List(Nil0{}); }

  static List<A> cons0(A a0, List<A> a1) {
    return List(Cons0{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons0>(_node.v_)) {
        auto &_alt = std::get<Cons0>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil0>(this->v())) {
      return true;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons0>(this->v());
      return (f(a0) && a1->forallb(f));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil0>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons0>(this->v());
      return f(a1, a2->template fold_right<T1>(f, a0));
    }
  }

  template <typename T1> List<T1> concat() const {
    if (std::holds_alternative<typename List<List<T1>>::Nil0>(this->v())) {
      return List<T1>::nil0();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<T1>>::Cons0>(this->v());
      return a0.app(a1->template concat<T1>());
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil0>(this->v())) {
      return List<T1>::nil0();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons0>(this->v());
      return List<T1>::cons0(f(a0), a1->template map<T1>(f));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil0>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons0>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil0>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons0>(this->v());
      return List<A>::cons0(a0, a1->app(std::move(m)));
    }
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename A> struct T0 {
  // TYPES
  struct Nil {};

  struct Cons {
    A h;
    uint64_t n;
    std::unique_ptr<T0<A>> a2;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T0() {}

  explicit T0(Nil _v) : v_(_v) {}

  explicit T0(Cons _v) : v_(std::move(_v)) {}

  T0(const T0<A> &_other) : v_(std::move(_other.clone().v_)) {}

  T0(T0<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  T0<A> &operator=(const T0<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  T0<A> &operator=(T0<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  T0<A> clone() const {
    if (std::holds_alternative<Nil>(this->v())) {
      return T0<A>(Nil{});
    } else {
      const auto &[h, n, a2] = std::get<Cons>(this->v());
      return T0<A>(
          Cons{h, n, a2 ? std::make_unique<T0<A>>(a2->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit T0(const T0<_U> &_other) {
    if (std::holds_alternative<typename T0<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[h, n, a2] = std::get<typename T0<_U>::Cons>(_other.v());
      this->v_ = Cons{A(h), n, a2 ? std::make_unique<T0<A>>(*a2) : nullptr};
    }
  }

  static T0<A> nil() { return T0(Nil{}); }

  static T0<A> cons(A h, uint64_t n, T0<A> a2) {
    return T0(Cons{std::move(h), n, std::make_unique<T0<A>>(std::move(a2))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct T {
  // TYPES
  struct F1 {
    uint64_t n;
  };

  struct FS {
    uint64_t n;
    std::unique_ptr<T> a1;
  };

  using variant_t = std::variant<F1, FS>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  T() {}

  explicit T(F1 _v) : v_(std::move(_v)) {}

  explicit T(FS _v) : v_(std::move(_v)) {}

  T(const T &_other) : v_(std::move(_other.clone().v_)) {}

  T(T &&_other) noexcept : v_(std::move(_other.v_)) {}

  T &operator=(const T &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  T &operator=(T &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  T clone() const {
    T _out{};

    struct _CloneFrame {
      const T *_src;
      T *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const T *_src = _frame._src;
      T *_dst = _frame._dst;
      if (std::holds_alternative<F1>(_src->v())) {
        const auto &_alt = std::get<F1>(_src->v());
        _dst->v_ = F1{_alt.n};
      } else {
        const auto &_alt = std::get<FS>(_src->v());
        _dst->v_ = FS{_alt.n, _alt.a1 ? std::make_unique<T>() : nullptr};
        auto &_dst_alt = std::get<FS>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static T f1(uint64_t n) { return T(F1{n}); }

  static T fs(uint64_t n, T a1) {
    return T(FS{n, std::make_unique<T>(std::move(a1))});
  }

  // MANIPULATORS
  ~T() {
    std::vector<std::unique_ptr<T>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](T &_node) {
      if (std::holds_alternative<FS>(_node.v_)) {
        auto &_alt = std::get<FS>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  Sig<uint64_t> to_nat(uint64_t) const {
    if (std::holds_alternative<typename T::F1>(this->v())) {
      return Sig<uint64_t>::exist(UINT64_C(0));
    } else {
      const auto &[n1, a1] = std::get<typename T::FS>(this->v());
      const auto &_sv0 = a1->to_nat(n1);
      const auto &[x0] = _sv0;
      return Sig<uint64_t>::exist((x0 + 1));
    }
  }
};

struct Fin {
  static T of_nat_lt(uint64_t p, uint64_t n);
};

struct Vector {
  template <typename T1> static List<T1> to_list(uint64_t n, const T0<T1> &v);
};

struct Datatypes {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static std::optional<T2> option_map(F0 &&f, const std::optional<T1> &o);
};

struct PendantSumtreeRoundtripCase {
  using digit = T;
  static uint64_t digit_to_nat(const T &d);
  static digit digit_of_nat(uint64_t n);
  static inline const digit digit0 = digit_of_nat(UINT64_C(0));
  static inline const digit digit1 = digit_of_nat(UINT64_C(1));
  static inline const digit digit2 = digit_of_nat(UINT64_C(2));
  static inline const digit digit3 = digit_of_nat(UINT64_C(3));
  static inline const digit digit4 = digit_of_nat(UINT64_C(4));
  static inline const digit digit5 = digit_of_nat(UINT64_C(5));
  static inline const digit digit6 = digit_of_nat(UINT64_C(6));
  static inline const digit digit7 = digit_of_nat(UINT64_C(7));
  static inline const digit digit9 = digit_of_nat(UINT64_C(9));
  static uint64_t value_digits(uint64_t _x, const T0<T> &ds);
  static std::optional<T0<digit>> list_to_vector_opt(uint64_t n,
                                                     const List<T> &xs);
  static List<List<digit>> encode_multi(uint64_t n, const List<T0<T>> &nums);
  static std::optional<List<T0<digit>>>
  decode_multi(uint64_t n, const List<List<T>> &segments);
  enum class Twist { TS, TZ };

  template <typename T1> static T1 Twist_rect(T1 f, T1 f0, Twist t1) {
    switch (t1) {
    case Twist::TS: {
      return f;
    }
    case Twist::TZ: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Twist_rec(T1 f, T1 f0, Twist t1) {
    switch (t1) {
    case Twist::TS: {
      return f;
    }
    case Twist::TZ: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }
  enum class Fiber { COTTON, CAMELID };

  template <typename T1> static T1 Fiber_rect(T1 f, T1 f0, Fiber f1) {
    switch (f1) {
    case Fiber::COTTON: {
      return f;
    }
    case Fiber::CAMELID: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 Fiber_rec(T1 f, T1 f0, Fiber f1) {
    switch (f1) {
    case Fiber::COTTON: {
      return f;
    }
    case Fiber::CAMELID: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }
  enum class Color { WHITE, BROWN, RED, BLUE };

  template <typename T1>
  static T1 Color_rect(T1 f, T1 f0, T1 f1, T1 f2, Color c) {
    switch (c) {
    case Color::WHITE: {
      return f;
    }
    case Color::BROWN: {
      return f0;
    }
    case Color::RED: {
      return f1;
    }
    case Color::BLUE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 Color_rec(T1 f, T1 f0, T1 f1, T1 f2, Color c) {
    switch (c) {
    case Color::WHITE: {
      return f;
    }
    case Color::BROWN: {
      return f0;
    }
    case Color::RED: {
      return f1;
    }
    case Color::BLUE: {
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

    // ACCESSORS
    CordMeta clone() const {
      return CordMeta{(*this).cm_fiber, (*this).cm_color, (*this).cm_spin,
                      (*this).cm_ply};
    }
  };

  struct CertifiedPendant {
    CordMeta cp_meta;
    T0<digit> cp_digits;

    // ACCESSORS
    CertifiedPendant clone() const {
      return CertifiedPendant{(*this).cp_meta.clone(),
                              (*this).cp_digits.clone()};
    }
  };

  static std::optional<T0<digit>> pendant_digits(uint64_t n,
                                                 const CertifiedPendant &p);
  static std::optional<uint64_t> pendant_value(uint64_t n,
                                               const CertifiedPendant &p);
  using Ledger = List<SigT<uint64_t, CertifiedPendant>>;
  static List<std::optional<uint64_t>>
  ledger_values(const List<SigT<uint64_t, CertifiedPendant>> &l);

  struct PendantGroup {
    CertifiedPendant pg_top;
    List<CertifiedPendant> pg_pendants;

    // ACCESSORS
    PendantGroup clone() const {
      return PendantGroup{(*this).pg_top.clone(), (*this).pg_pendants.clone()};
    }
  };

  static bool group_sums_validb(uint64_t n, const PendantGroup &g);

  struct SumTree {
    // TYPES
    struct SumLeaf {
      CertifiedPendant a0;
    };

    struct SumNode {
      CertifiedPendant a0;
      std::unique_ptr<List<SumTree>> a1;
    };

    using variant_t = std::variant<SumLeaf, SumNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    SumTree() {}

    explicit SumTree(SumLeaf _v) : v_(std::move(_v)) {}

    explicit SumTree(SumNode _v) : v_(std::move(_v)) {}

    SumTree(const SumTree &_other) : v_(std::move(_other.clone().v_)) {}

    SumTree(SumTree &&_other) noexcept : v_(std::move(_other.v_)) {}

    SumTree &operator=(const SumTree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    SumTree &operator=(SumTree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    SumTree clone() const {
      SumTree _out{};

      struct _CloneFrame {
        const SumTree *_src;
        SumTree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const SumTree *_src = _frame._src;
        SumTree *_dst = _frame._dst;
        if (std::holds_alternative<SumLeaf>(_src->v())) {
          const auto &_alt = std::get<SumLeaf>(_src->v());
          _dst->v_ = SumLeaf{_alt.a0.clone()};
        } else {
          const auto &_alt = std::get<SumNode>(_src->v());
          _dst->v_ =
              SumNode{_alt.a0.clone(),
                      _alt.a1 ? std::make_unique<List<SumTree>>() : nullptr};
          auto &_dst_alt = std::get<SumNode>(_dst->v_);
          [&] {
            if (_alt.a1) {
              const List<SumTree> *_lsrc = _alt.a1.get();
              List<SumTree> *_ldst = _dst_alt.a1.get();
              while (std::holds_alternative<typename List<SumTree>::Cons0>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<SumTree>::Cons0>(_lsrc->v());
                _ldst->v_mut() = typename List<SumTree>::Cons0{
                    SumTree{},
                    _lsrc_c.a1 ? std::make_unique<List<SumTree>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<SumTree>::Cons0>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
                if (_lsrc_c.a1) {
                  _lsrc = _lsrc_c.a1.get();
                  _ldst = _ldst_c.a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<typename List<SumTree>::Nil0>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<SumTree>::Nil0{};
              }
            }
          }();
        }
      }
      return _out;
    }

    // CREATORS
    static SumTree sumleaf(CertifiedPendant a0) {
      return SumTree(SumLeaf{std::move(a0)});
    }

    static SumTree sumnode(CertifiedPendant a0, List<SumTree> a1) {
      return SumTree(SumNode{std::move(a0),
                             std::make_unique<List<SumTree>>(std::move(a1))});
    }

    // MANIPULATORS
    ~SumTree() {
      std::vector<std::unique_ptr<SumTree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](SumTree &_node) {
        if (std::holds_alternative<SumNode>(_node.v_)) {
          auto &_alt = std::get<SumNode>(_node.v_);
          if (_alt.a1) {
            auto *_lp = _alt.a1.get();
            while (std::holds_alternative<typename List<SumTree>::Cons0>(
                _lp->v())) {
              auto &_lc = std::get<typename List<SumTree>::Cons0>(_lp->v_mut());
              _stack.push_back(std::make_unique<SumTree>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
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

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, CertifiedPendant &> &&
             std::is_invocable_r_v<T1, F2 &, CertifiedPendant &,
                                   List<SumTree> &>
  static T1 SumTree_rect(uint64_t, F1 &&f, F2 &&f0, const SumTree &s) {
    if (std::holds_alternative<typename SumTree::SumLeaf>(s.v())) {
      const auto &[a0] = std::get<typename SumTree::SumLeaf>(s.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename SumTree::SumNode>(s.v());
      return f0(a0, *a1);
    }
  }

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, CertifiedPendant &> &&
             std::is_invocable_r_v<T1, F2 &, CertifiedPendant &,
                                   List<SumTree> &>
  static T1 SumTree_rec(uint64_t, F1 &&f, F2 &&f0, const SumTree &s) {
    if (std::holds_alternative<typename SumTree::SumLeaf>(s.v())) {
      const auto &[a0] = std::get<typename SumTree::SumLeaf>(s.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename SumTree::SumNode>(s.v());
      return f0(a0, *a1);
    }
  }

  static CertifiedPendant sumtree_top(uint64_t _x, const SumTree &st);
  static List<CertifiedPendant> sumtree_leaves(uint64_t n, const SumTree &st);
  static uint64_t sumtree_depth(uint64_t n, const SumTree &st);
  static bool sumtree_validb_aux(uint64_t n, uint64_t fuel, const SumTree &st);
  static bool sumtree_validb(uint64_t n, const SumTree &st);
  static std::optional<uint64_t> sumtree_leaf_total(uint64_t n,
                                                    const SumTree &st);
  static bool nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys);
  static bool option_nat_eqb(const std::optional<uint64_t> &x,
                             const std::optional<uint64_t> &y);
  static bool option_nat_is_some(const std::optional<uint64_t> &x);
  static T0<digit> digit_vec1(T a);
  static T0<digit> digit_vec3(T a, T b, T c);
  static inline const CordMeta sample_meta_a =
      CordMeta{Fiber::COTTON, Color::BROWN, Twist::TS, Twist::TZ};
  static inline const CordMeta sample_meta_b =
      CordMeta{Fiber::CAMELID, Color::RED, Twist::TZ, Twist::TS};
  static inline const CordMeta sample_meta_c =
      CordMeta{Fiber::COTTON, Color::BLUE, Twist::TS, Twist::TS};
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
    auto _cs = decode_multi(UINT64_C(3),
                            encode_multi(UINT64_C(3), sample_multi_digits));
    if (_cs.has_value()) {
      const List<T0<T>> &decoded = *_cs;
      return nat_list_eqb(
          decoded.template map<uint64_t>([](T0<digit> _x0) -> uint64_t {
            return value_digits(UINT64_C(3), _x0);
          }),
          List<uint64_t>::cons0(
              UINT64_C(731),
              List<uint64_t>::cons0(
                  UINT64_C(462), List<uint64_t>::cons0(
                                     UINT64_C(269), List<uint64_t>::nil0()))));
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
      List<SigT<uint64_t, CertifiedPendant>>::cons0(
          SigT<uint64_t, CertifiedPendant>::existt(UINT64_C(3), pendant_731),
          List<SigT<uint64_t, CertifiedPendant>>::cons0(
              SigT<uint64_t, CertifiedPendant>::existt(UINT64_C(3),
                                                       pendant_462),
              List<SigT<uint64_t, CertifiedPendant>>::cons0(
                  SigT<uint64_t, CertifiedPendant>::existt(UINT64_C(1),
                                                           pendant_5),
                  List<SigT<uint64_t, CertifiedPendant>>::nil0())));
  static inline const bool sample_group_valid =
      group_sums_validb(UINT64_C(3), sample_group);
  static inline const bool sample_subtree_valid =
      sumtree_validb(UINT64_C(3), sample_subtree);
  static inline const bool sample_tree_valid =
      sumtree_validb(UINT64_C(3), sample_tree);
  static inline const bool sample_leaf_total_matches_root =
      option_nat_eqb(sumtree_leaf_total(UINT64_C(3), sample_tree),
                     pendant_value(UINT64_C(3), pendant_731));
  static inline const uint64_t sample_tree_depth =
      sumtree_depth(UINT64_C(3), sample_tree);
  static inline const uint64_t sample_ledger_entry_count =
      ledger_values(sample_ledger).length();
  static inline const bool sample_ledger_all_present =
      ledger_values(sample_ledger).forallb(option_nat_is_some);
};

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
std::optional<T2> Datatypes::option_map(F0 &&f, const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &a = *o;
    return std::make_optional<T2>(f(a));
  } else {
    return std::optional<T2>();
  }
}

template <typename T1> List<T1> Vector::to_list(uint64_t n, const T0<T1> &v) {
  auto fold_right_fix_impl = [](auto &_self_fold_right_fix, uint64_t,
                                const T0<T1> &v0, List<T1> b) -> List<T1> {
    if (std::holds_alternative<typename T0<T1>::Nil>(v0.v())) {
      return b;
    } else {
      const auto &[h, n1, a2] = std::get<typename T0<T1>::Cons>(v0.v());
      return List<T1>::cons0(
          h, _self_fold_right_fix(_self_fold_right_fix, n1, *a2, std::move(b)));
    }
  };
  auto fold_right_fix = [&](uint64_t _x, const T0<T1> &v0,
                            List<T1> b) -> List<T1> {
    return fold_right_fix_impl(fold_right_fix_impl, _x, v0, b);
  };
  return fold_right_fix(n, v, List<T1>::nil0());
}

#endif // INCLUDED_PENDANT_SUMTREE_ROUNDTRIP
