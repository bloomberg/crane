#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct DeepPatterns {
  static uint64_t
  deep_option(const std::optional<std::optional<std::optional<uint64_t>>> &x);
  static uint64_t deep_pair(const std::pair<std::pair<uint64_t, uint64_t>,
                                            std::pair<uint64_t, uint64_t>> &p);
  static uint64_t list_shape(const List<uint64_t> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::unique_ptr<inner> a0;
    };

    struct ORight {
      uint64_t a0;
    };

    using variant_t = std::variant<OLeft, ORight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeft _v) : v_(std::move(_v)) {}

    explicit outer(ORight _v) : v_(std::move(_v)) {}

    outer(const outer &_other) : v_(std::move(_other.clone().v_)) {}

    outer(outer &&_other) noexcept : v_(std::move(_other.v_)) {}

    outer &operator=(const outer &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    outer &operator=(outer &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    outer clone() const {
      if (std::holds_alternative<OLeft>(this->v())) {
        const auto &[a0] = std::get<OLeft>(this->v());
        return outer(OLeft{
            a0 ? std::make_unique<DeepPatterns::inner>(a0->clone()) : nullptr});
      } else {
        const auto &[a0] = std::get<ORight>(this->v());
        return outer(ORight{a0});
      }
    }

    // CREATORS
    static outer oleft(inner a0) {
      return outer(OLeft{std::make_unique<inner>(std::move(a0))});
    }

    static outer oright(uint64_t a0) { return outer(ORight{a0}); }

    // MANIPULATORS
    ~outer() {
      std::vector<std::unique_ptr<outer>> _stack{};
      _stack.reserve(8);
      auto _drain = [](outer &_node) {
        if (std::holds_alternative<OLeft>(_node.v_)) {
          auto &_alt = std::get<OLeft>(_node.v_);
          if (_alt.a0) {
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

  struct inner {
    // TYPES
    struct ILeft {
      uint64_t a0;
    };

    struct IRight {
      bool a0;
    };

    using variant_t = std::variant<ILeft, IRight>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeft _v) : v_(std::move(_v)) {}

    explicit inner(IRight _v) : v_(std::move(_v)) {}

    inner(const inner &_other) : v_(std::move(_other.clone().v_)) {}

    inner(inner &&_other) noexcept : v_(std::move(_other.v_)) {}

    inner &operator=(const inner &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    inner &operator=(inner &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    inner clone() const {
      if (std::holds_alternative<ILeft>(this->v())) {
        const auto &[a0] = std::get<ILeft>(this->v());
        return inner(ILeft{a0});
      } else {
        const auto &[a0] = std::get<IRight>(this->v());
        return inner(IRight{a0});
      }
    }

    // CREATORS
    static inner ileft(uint64_t a0) { return inner(ILeft{a0}); }

    static inner iright(bool a0) { return inner(IRight{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 outer_rect(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[a0] = std::get<typename outer::OLeft>(o.v());
      return f(*a0);
    } else {
      const auto &[a0] = std::get<typename outer::ORight>(o.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 outer_rec(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[a0] = std::get<typename outer::OLeft>(o.v());
      return f(*a0);
    } else {
      const auto &[a0] = std::get<typename outer::ORight>(o.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 inner_rect(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[a0] = std::get<typename inner::ILeft>(i.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename inner::IRight>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, bool &>
  static T1 inner_rec(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[a0] = std::get<typename inner::ILeft>(i.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename inner::IRight>(i.v());
      return f0(a0);
    }
  }

  static uint64_t deep_sum(const outer &o);
  static uint64_t
  complex_match(const std::optional<std::pair<uint64_t, List<uint64_t>>> &x);
  static uint64_t guarded_match(const std::pair<uint64_t, uint64_t> &p);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rec(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Nil _v) : v_(_v) {}

    explicit mylist(Cons _v) : v_(std::move(_v)) {}

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->v_ =
              Cons{_alt.a0, _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename mylist<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> nil() { return mylist(Nil{}); }

    static mylist<A> cons(A a0, mylist<A> a1) {
      return mylist(
          Cons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Cons>(_node.v_)) {
          auto &_alt = std::get<Cons>(_node.v_);
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

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t match_pair_list(const mylist<pair<uint64_t, uint64_t>> &l);
  static uint64_t match_two(const mylist<uint64_t> &l);
  static uint64_t match_triple(const mylist<mylist<mylist<uint64_t>>> &l);
  static uint64_t deep_wildcard(
      const pair<pair<uint64_t, uint64_t>, pair<uint64_t, uint64_t>> &p);
  static inline const uint64_t test_deep_some =
      deep_option(std::make_optional<std::optional<std::optional<uint64_t>>>(
          std::make_optional<std::optional<uint64_t>>(
              std::make_optional<uint64_t>(UINT64_C(42)))));
  static inline const uint64_t test_deep_none =
      deep_option(std::make_optional<std::optional<std::optional<uint64_t>>>(
          std::make_optional<std::optional<uint64_t>>(
              std::optional<uint64_t>())));
  static inline const uint64_t test_deep_pair =
      deep_pair(std::make_pair(std::make_pair(UINT64_C(1), UINT64_C(2)),
                               std::make_pair(UINT64_C(3), UINT64_C(4))));
  static inline const uint64_t test_shape_3 = list_shape(List<uint64_t>::cons(
      UINT64_C(10),
      List<uint64_t>::cons(
          UINT64_C(20),
          List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const uint64_t test_shape_long =
      list_shape(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil())))))));
  static inline const uint64_t test_deep_sum =
      deep_sum(outer::oleft(inner::ileft(UINT64_C(77))));
  static inline const uint64_t test_complex = complex_match(
      std::make_optional<std::pair<uint64_t, List<uint64_t>>>(std::make_pair(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(10),
              List<uint64_t>::cons(
                  UINT64_C(20), List<uint64_t>::cons(
                                    UINT64_C(30), List<uint64_t>::nil()))))));
  static inline const uint64_t test_guarded =
      guarded_match(std::make_pair(UINT64_C(3), UINT64_C(7)));
  static inline const uint64_t test_pair_list =
      match_pair_list(mylist<pair<uint64_t, uint64_t>>::cons(
          pair<uint64_t, uint64_t>::pair0(UINT64_C(5), UINT64_C(3)),
          mylist<pair<uint64_t, uint64_t>>::nil()));
  static inline const uint64_t test_two_one =
      match_two(mylist<uint64_t>::cons(UINT64_C(7), mylist<uint64_t>::nil()));
  static inline const uint64_t test_two_many = match_two(mylist<uint64_t>::cons(
      UINT64_C(7),
      mylist<uint64_t>::cons(UINT64_C(8), mylist<uint64_t>::nil())));
  static inline const uint64_t test_triple =
      match_triple(mylist<mylist<mylist<uint64_t>>>::cons(
          mylist<mylist<uint64_t>>::cons(
              mylist<uint64_t>::cons(UINT64_C(9), mylist<uint64_t>::nil()),
              mylist<mylist<uint64_t>>::nil()),
          mylist<mylist<mylist<uint64_t>>>::nil()));
  static inline const uint64_t test_wildcard = deep_wildcard(
      pair<pair<uint64_t, uint64_t>, pair<uint64_t, uint64_t>>::pair0(
          pair<uint64_t, uint64_t>::pair0(UINT64_C(1), UINT64_C(2)),
          pair<uint64_t, uint64_t>::pair0(UINT64_C(3), UINT64_C(4))));
  static inline const uint64_t t =
      ((((((((((((test_deep_some + test_deep_none) + test_deep_pair) +
                test_shape_3) +
               test_shape_long) +
              test_deep_sum) +
             test_complex) +
            test_guarded) +
           test_pair_list) +
          test_two_one) +
         test_two_many) +
        test_triple) +
       test_wildcard);
};

#endif // INCLUDED_DEEP_PATTERNS
