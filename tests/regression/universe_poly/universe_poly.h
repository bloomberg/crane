#ifndef INCLUDED_UNIVERSE_POLY
#define INCLUDED_UNIVERSE_POLY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

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
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct UniversePoly {
  template <typename T1> static T1 poly_id(T1 x) { return x; }

  static inline const uint64_t test_id_nat = poly_id<uint64_t>(UINT64_C(42));
  static inline const bool test_id_bool = poly_id<bool>(true);

  template <typename A, typename B> struct ppair {
    A pfst;
    B psnd;

    // ACCESSORS
    ppair<A, B> clone() const { return ppair<A, B>{this->pfst, this->psnd}; }
  };

  static inline const ppair<uint64_t, bool> test_pair =
      ppair<uint64_t, bool>{UINT64_C(5), true};
  static inline const uint64_t test_pfst = test_pair.pfst;
  static inline const bool test_psnd = test_pair.psnd;

  template <typename A> struct poption {
    // TYPES
    struct Pnone {};

    struct Psome {
      A a0;
    };

    using variant_t = std::variant<Pnone, Psome>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    poption() {}

    explicit poption(Pnone _v) : v_(_v) {}

    explicit poption(Psome _v) : v_(std::move(_v)) {}

    poption(const poption<A> &_other) : v_(_other.v_) {}

    poption(poption<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    poption<A> &operator=(const poption<A> &_other) {
      v_ = _other.v_;
      return *this;
    }

    poption<A> &operator=(poption<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    poption<A> clone() const {
      if (std::holds_alternative<Pnone>(this->v())) {
        return poption<A>(Pnone{});
      } else {
        const auto &[a0] = std::get<Psome>(this->v());
        return poption<A>(Psome{a0});
      }
    }

    // CREATORS
    template <typename _U> explicit poption(const poption<_U> &_other) {
      if (std::holds_alternative<typename poption<_U>::Pnone>(_other.v())) {
        this->v_ = Pnone{};
      } else {
        const auto &[a0] = std::get<typename poption<_U>::Psome>(_other.v());
        this->v_ = Psome{A(a0)};
      }
    }

    static poption<A> pnone() { return poption(Pnone{}); }

    static poption<A> psome(A a0) { return poption(Psome{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &>
  static T2 poption_rect(T2 f, F1 &&f0, const poption<T1> &p) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(p.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename poption<T1>::Psome>(p.v());
      return f0(a0);
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &>
  static T2 poption_rec(T2 f, F1 &&f0, const poption<T1> &p) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(p.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename poption<T1>::Psome>(p.v());
      return f0(a0);
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static poption<T2> poption_map(F0 &&f, const poption<T1> &o) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(o.v())) {
      return poption<T2>::pnone();
    } else {
      const auto &[a0] = std::get<typename poption<T1>::Psome>(o.v());
      return poption<T2>::psome(f(a0));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<poption<T2>, F1 &, T1 &>
  static poption<T2> poption_bind(const poption<T1> &o, F1 &&f) {
    if (std::holds_alternative<typename poption<T1>::Pnone>(o.v())) {
      return poption<T2>::pnone();
    } else {
      const auto &[a0] = std::get<typename poption<T1>::Psome>(o.v());
      return f(a0);
    }
  }

  static inline const poption<uint64_t> test_map_some =
      poption_map<uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          poption<uint64_t>::psome(UINT64_C(5)));
  static inline const poption<uint64_t> test_map_none =
      poption_map<uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          poption<uint64_t>::pnone());
  static inline const poption<uint64_t> test_bind =
      poption_bind<uint64_t, uint64_t>(
          poption<uint64_t>::psome(UINT64_C(3)),
          [](uint64_t n) { return poption<uint64_t>::psome((n + n)); });

  template <typename T1> static uint64_t poly_length(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return (poly_length<T1>(*a1) + 1);
    }
  }

  static inline const uint64_t test_length =
      poly_length<uint64_t>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
};

#endif // INCLUDED_UNIVERSE_POLY
