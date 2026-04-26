#ifndef INCLUDED_DEEP_PATTERNS
#define INCLUDED_DEEP_PATTERNS

#include <memory>
#include <optional>
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

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

struct DeepPatterns {
  __attribute__((pure)) static unsigned int deep_option(
      const std::optional<std::optional<std::optional<unsigned int>>> &x);
  __attribute__((pure)) static unsigned int
  deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                            std::pair<unsigned int, unsigned int>> &p);
  __attribute__((pure)) static unsigned int
  list_shape(const List<unsigned int> &l);
  struct outer;
  struct inner;

  struct outer {
    // TYPES
    struct OLeft {
      std::unique_ptr<inner> d_a0;
    };

    struct ORight {
      unsigned int d_a0;
    };

    using variant_t = std::variant<OLeft, ORight>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeft _v) : d_v_(std::move(_v)) {}

    explicit outer(ORight _v) : d_v_(std::move(_v)) {}

    outer(const outer &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    outer(outer &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) outer &operator=(const outer &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) outer &operator=(outer &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) outer clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<OLeft>(_sv.v())) {
        const auto &[d_a0] = std::get<OLeft>(_sv.v());
        return outer(OLeft{clone_as_value<std::unique_ptr<inner>>(d_a0)});
      } else {
        const auto &[d_a0] = std::get<ORight>(_sv.v());
        return outer(ORight{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static outer oleft(const inner &a0) {
      return outer(OLeft{std::make_unique<inner>(a0.clone())});
    }

    __attribute__((pure)) static outer oright(unsigned int a0) {
      return outer(ORight{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) outer *operator->() { return this; }

    __attribute__((pure)) const outer *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = outer(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct inner {
    // TYPES
    struct ILeft {
      unsigned int d_a0;
    };

    struct IRight {
      bool d_a0;
    };

    using variant_t = std::variant<ILeft, IRight>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeft _v) : d_v_(std::move(_v)) {}

    explicit inner(IRight _v) : d_v_(std::move(_v)) {}

    inner(const inner &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    inner(inner &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) inner &operator=(const inner &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) inner &operator=(inner &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) inner clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ILeft>(_sv.v())) {
        const auto &[d_a0] = std::get<ILeft>(_sv.v());
        return inner(ILeft{d_a0});
      } else {
        const auto &[d_a0] = std::get<IRight>(_sv.v());
        return inner(IRight{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static inner ileft(unsigned int a0) {
      return inner(ILeft{std::move(a0)});
    }

    constexpr static inner iright(bool a0) {
      return inner(IRight{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) inner *operator->() { return this; }

    __attribute__((pure)) const inner *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = inner(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, inner> F0, MapsTo<T1, unsigned int> F1>
  static T1 outer_rect(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[d_a0] = std::get<typename outer::OLeft>(o.v());
      return f(*(d_a0));
    } else {
      const auto &[d_a0] = std::get<typename outer::ORight>(o.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, inner> F0, MapsTo<T1, unsigned int> F1>
  static T1 outer_rec(F0 &&f, F1 &&f0, const outer &o) {
    if (std::holds_alternative<typename outer::OLeft>(o.v())) {
      const auto &[d_a0] = std::get<typename outer::OLeft>(o.v());
      return f(*(d_a0));
    } else {
      const auto &[d_a0] = std::get<typename outer::ORight>(o.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rect(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[d_a0] = std::get<typename inner::ILeft>(i.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename inner::IRight>(i.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, bool> F1>
  static T1 inner_rec(F0 &&f, F1 &&f0, const inner &i) {
    if (std::holds_alternative<typename inner::ILeft>(i.v())) {
      const auto &[d_a0] = std::get<typename inner::ILeft>(i.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename inner::IRight>(i.v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static unsigned int deep_sum(const outer &o);
  __attribute__((pure)) static unsigned int complex_match(
      const std::optional<std::pair<unsigned int, List<unsigned int>>> &x);
  __attribute__((pure)) static unsigned int
  guarded_match(const std::pair<unsigned int, unsigned int> &p);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    pair(const pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair(pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) pair<t_A, t_B> &
    operator=(const pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) pair<t_A, t_B> &operator=(pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<t_A, t_B>(
          Pair0{clone_as_value<t_A>(d_a0), clone_as_value<t_B>(d_a1)});
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) pair<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<_CloneT0, _CloneT1>(typename pair<_CloneT0, _CloneT1>::Pair0{
          clone_as_value<_CloneT0>(d_a0), clone_as_value<_CloneT1>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static pair<t_A, t_B> pair0(t_A a0, t_B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const pair<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pair<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  template <typename t_A> struct mylist {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Nil _v) : d_v_(_v) {}

    explicit mylist(Cons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return mylist<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return mylist<t_A>(
            Cons{clone_as_value<t_A>(d_a0),
                 clone_as_value<std::unique_ptr<mylist<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) mylist<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return mylist<_CloneT0>(typename mylist<_CloneT0>::Cons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<mylist<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static mylist<t_A> nil() { return mylist(Nil{}); }

    __attribute__((pure)) static mylist<t_A> cons(t_A a0,
                                                  const mylist<t_A> &a1) {
      return mylist(
          Cons{std::move(a0), std::make_unique<mylist<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mylist<t_A> *operator->() { return this; }

    __attribute__((pure)) const mylist<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mylist<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, mylist<t_A>, T1> F1>
    T1 mylist_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename mylist<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template mylist_rect<T1>(f, f0));
      }
    }
  };

  __attribute__((pure)) static unsigned int
  match_pair_list(const mylist<pair<unsigned int, unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  match_two(const mylist<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  match_triple(const mylist<mylist<mylist<unsigned int>>> &l);
  __attribute__((pure)) static unsigned int
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
