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
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
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

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct DeepPatterns {
  static unsigned int deep_option(
      const std::optional<std::optional<std::optional<unsigned int>>> &x);
  static unsigned int
  deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                            std::pair<unsigned int, unsigned int>> &p);
  static unsigned int list_shape(const List<unsigned int> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::unique_ptr<inner> a0;
    };

    struct ORight {
      unsigned int a0;
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

    outer(outer &&_other) : v_(std::move(_other.v_)) {}

    outer &operator=(const outer &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    outer &operator=(outer &&_other) {
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

    static outer oright(unsigned int a0) { return outer(ORight{a0}); }

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
      unsigned int a0;
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

    inner(inner &&_other) : v_(std::move(_other.v_)) {}

    inner &operator=(const inner &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    inner &operator=(inner &&_other) {
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
    static inner ileft(unsigned int a0) { return inner(ILeft{a0}); }

    static inner iright(bool a0) { return inner(IRight{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, inner &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
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
             std::is_invocable_r_v<T1, F1 &, unsigned int &>
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
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
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
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
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

  static unsigned int deep_sum(const outer &o);
  static unsigned int complex_match(
      const std::optional<std::pair<unsigned int, List<unsigned int>>> &x);
  static unsigned int
  guarded_match(const std::pair<unsigned int, unsigned int> &p);

  template <typename A, typename B> struct pair {
    // TYPES
    struct Pair0 {
      A a0;
      B a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : v_(std::move(_v)) {}

    pair(const pair<A, B> &_other) : v_(std::move(_other.clone().v_)) {}

    pair(pair<A, B> &&_other) : v_(std::move(_other.v_)) {}

    pair<A, B> &operator=(const pair<A, B> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    pair<A, B> &operator=(pair<A, B> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    pair<A, B> clone() const {
      const auto &[a0, a1] = std::get<Pair0>(this->v());
      return pair<A, B>(Pair0{a0, a1});
    }

    // CREATORS
    template <typename _U0, typename _U1>
    explicit pair(const pair<_U0, _U1> &_other) {
      const auto &[a0, a1] =
          std::get<typename pair<_U0, _U1>::Pair0>(_other.v());
      this->v_ = Pair0{A(a0), B(a1)};
    }

    static pair<A, B> pair0(A a0, B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename pair<A, B>::Pair0>(this->v());
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename pair<A, B>::Pair0>(this->v());
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

    mylist(mylist<A> &&_other) : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) {
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
        return f0(a0, *a1, (*a1).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Cons>(this->v());
        return f0(a0, *a1, (*a1).template mylist_rect<T1>(f, f0));
      }
    }
  };

  static unsigned int
  match_pair_list(const mylist<pair<unsigned int, unsigned int>> &l);
  static unsigned int match_two(const mylist<unsigned int> &l);
  static unsigned int
  match_triple(const mylist<mylist<mylist<unsigned int>>> &l);
  static unsigned int
  deep_wildcard(const pair<pair<unsigned int, unsigned int>,
                           pair<unsigned int, unsigned int>> &p);
  static inline const unsigned int test_deep_some = deep_option(
      std::make_optional<std::optional<std::optional<unsigned int>>>(
          std::make_optional<std::optional<unsigned int>>(
              std::make_optional<unsigned int>(42u))));
  static inline const unsigned int test_deep_none = deep_option(
      std::make_optional<std::optional<std::optional<unsigned int>>>(
          std::make_optional<std::optional<unsigned int>>(
              std::optional<unsigned int>())));
  static inline const unsigned int test_deep_pair =
      deep_pair(std::make_pair(std::make_pair(1u, 2u), std::make_pair(3u, 4u)));
  static inline const unsigned int test_shape_3 =
      list_shape(List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              20u, List<unsigned int>::cons(30u, List<unsigned int>::nil()))));
  static inline const unsigned int test_shape_long =
      list_shape(List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u,
              List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          4u, List<unsigned int>::cons(
                                  5u, List<unsigned int>::cons(
                                          6u, List<unsigned int>::nil())))))));
  static inline const unsigned int test_deep_sum =
      deep_sum(outer::oleft(inner::ileft(77u)));
  static inline const unsigned int test_complex = complex_match(
      std::make_optional<std::pair<unsigned int, List<unsigned int>>>(
          std::make_pair(
              5u, List<unsigned int>::cons(
                      10u, List<unsigned int>::cons(
                               20u, List<unsigned int>::cons(
                                        30u, List<unsigned int>::nil()))))));
  static inline const unsigned int test_guarded =
      guarded_match(std::make_pair(3u, 7u));
  static inline const unsigned int test_pair_list =
      match_pair_list(mylist<pair<unsigned int, unsigned int>>::cons(
          pair<unsigned int, unsigned int>::pair0(5u, 3u),
          mylist<pair<unsigned int, unsigned int>>::nil()));
  static inline const unsigned int test_two_one =
      match_two(mylist<unsigned int>::cons(7u, mylist<unsigned int>::nil()));
  static inline const unsigned int test_two_many =
      match_two(mylist<unsigned int>::cons(
          7u, mylist<unsigned int>::cons(8u, mylist<unsigned int>::nil())));
  static inline const unsigned int test_triple =
      match_triple(mylist<mylist<mylist<unsigned int>>>::cons(
          mylist<mylist<unsigned int>>::cons(
              mylist<unsigned int>::cons(9u, mylist<unsigned int>::nil()),
              mylist<mylist<unsigned int>>::nil()),
          mylist<mylist<mylist<unsigned int>>>::nil()));
  static inline const unsigned int test_wildcard = deep_wildcard(
      pair<pair<unsigned int, unsigned int>, pair<unsigned int, unsigned int>>::
          pair0(pair<unsigned int, unsigned int>::pair0(1u, 2u),
                pair<unsigned int, unsigned int>::pair0(3u, 4u)));
  static inline const unsigned int t =
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
