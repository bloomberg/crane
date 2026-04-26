#ifndef INCLUDED_NESTED_IND
#define INCLUDED_NESTED_IND

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

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

struct NestedInd {
  template <typename t_A> struct custom_list {
    // TYPES
    struct Cnil {};

    struct Ccons {
      t_A d_a0;
      std::unique_ptr<custom_list<t_A>> d_a1;
    };

    using variant_t = std::variant<Cnil, Ccons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    custom_list() {}

    explicit custom_list(Cnil _v) : d_v_(_v) {}

    explicit custom_list(Ccons _v) : d_v_(std::move(_v)) {}

    custom_list(const custom_list<t_A> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    custom_list(custom_list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) custom_list<t_A> &
    operator=(const custom_list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) custom_list<t_A> &
    operator=(custom_list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) custom_list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Cnil>(_sv.v())) {
        return custom_list<t_A>(Cnil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Ccons>(_sv.v());
        return custom_list<t_A>(
            Ccons{clone_as_value<t_A>(d_a0),
                  clone_as_value<std::unique_ptr<custom_list<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) custom_list<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Cnil>(_sv.v())) {
        return custom_list<_CloneT0>(typename custom_list<_CloneT0>::Cnil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Ccons>(_sv.v());
        return custom_list<_CloneT0>(typename custom_list<_CloneT0>::Ccons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<custom_list<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static custom_list<t_A> cnil() {
      return custom_list(Cnil{});
    }

    __attribute__((pure)) static custom_list<t_A>
    ccons(t_A a0, const custom_list<t_A> &a1) {
      return custom_list(
          Ccons{std::move(a0), std::make_unique<custom_list<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) custom_list<t_A> *operator->() { return this; }

    __attribute__((pure)) const custom_list<t_A> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = custom_list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int custom_list_length() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return (1u + (*(d_a1)).custom_list_length());
      }
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<t_A>, T1> F1>
    T1 custom_list_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template custom_list_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<t_A>, T1> F1>
    T1 custom_list_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename custom_list<t_A>::Cnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename custom_list<t_A>::Ccons>(_sv.v());
        return f0(d_a0, *(d_a1),
                  (*(d_a1)).template custom_list_rect<T1>(f, f0));
      }
    }
  };

  template <typename t_A> struct rose {
    // TYPES
    struct Node {
      t_A d_a0;
      custom_list<std::unique_ptr<rose<t_A>>> d_a1;
    };

    using variant_t = std::variant<Node>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(Node _v) : d_v_(std::move(_v)) {}

    rose(const rose<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    rose(rose<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) rose<t_A> &operator=(const rose<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) rose<t_A> &operator=(rose<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) rose<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
      return rose<t_A>(Node{clone_as_value<t_A>(d_a0), d_a1});
    }

    template <typename _CloneT0>
    __attribute__((pure)) rose<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
      return rose<_CloneT0>(typename rose<_CloneT0>::Node{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<custom_list<std::unique_ptr<rose<_CloneT0>>>>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static rose<t_A> node(t_A a0,
                                                custom_list<rose<t_A>> a1) {
      return rose(
          Node{std::move(a0),
               clone_as_value<custom_list<std::unique_ptr<rose<t_A>>>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) rose<t_A> *operator->() { return this; }

    __attribute__((pure)) const rose<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = rose<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int children_count() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return clone_as_value<NestedInd::custom_list<NestedInd::rose<t_A>>>(d_a1)
          .custom_list_length();
    }

    t_A root() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return d_a0;
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<rose<t_A>>> F0>
    T1 rose_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return f(
          d_a0,
          clone_as_value<NestedInd::custom_list<NestedInd::rose<t_A>>>(d_a1));
    }

    template <typename T1, MapsTo<T1, t_A, custom_list<rose<t_A>>> F0>
    T1 rose_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose<t_A>::Node>(_sv.v());
      return f(
          d_a0,
          clone_as_value<NestedInd::custom_list<NestedInd::rose<t_A>>>(d_a1));
    }
  };

  __attribute__((pure)) static rose<unsigned int> leaf(unsigned int n);
  static inline const rose<unsigned int> small_tree = rose<unsigned int>::node(
      1u,
      custom_list<rose<unsigned int>>::ccons(
          leaf(2u), custom_list<rose<unsigned int>>::ccons(
                        leaf(3u), custom_list<rose<unsigned int>>::cnil())));
  static inline const rose<unsigned int> bigger_tree = rose<unsigned int>::node(
      1u,
      custom_list<rose<unsigned int>>::ccons(
          small_tree, custom_list<rose<unsigned int>>::ccons(
                          leaf(4u), custom_list<rose<unsigned int>>::cnil())));
  static inline const unsigned int test_root_leaf = leaf(5u).root();
  static inline const unsigned int test_root_small = small_tree.root();
  static inline const unsigned int test_children_leaf =
      leaf(5u).children_count();
  static inline const unsigned int test_children_small =
      small_tree.children_count();
  static inline const unsigned int test_children_bigger =
      bigger_tree.children_count();

  struct expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Add {
      List<std::unique_ptr<expr>> d_a0;
    };

    struct Mul {
      List<std::unique_ptr<expr>> d_a0;
    };

    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    expr(const expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    expr(expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<Lit>(_sv.v());
        return expr(Lit{d_a0});
      } else if (std::holds_alternative<Add>(_sv.v())) {
        const auto &[d_a0] = std::get<Add>(_sv.v());
        return expr(Add{d_a0});
      } else {
        const auto &[d_a0] = std::get<Mul>(_sv.v());
        return expr(Mul{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static expr lit(unsigned int a0) {
      return expr(Lit{std::move(a0)});
    }

    __attribute__((pure)) static expr add(List<expr> a0) {
      return expr(Add{clone_as_value<List<std::unique_ptr<expr>>>(a0)});
    }

    __attribute__((pure)) static expr mul(List<expr> a0) {
      return expr(Mul{clone_as_value<List<std::unique_ptr<expr>>>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) expr *operator->() { return this; }

    __attribute__((pure)) const expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <MapsTo<unsigned int, unsigned int> F0>
    __attribute__((pure)) expr lit_map(F0 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return expr::lit(f(d_a0));
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return expr::add([&]() {
          std::function<List<expr>(List<expr>)> aux;
          aux = [&](List<expr> l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(d_a0.lit_map(f), aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }());
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return expr::mul([&]() {
          std::function<List<expr>(List<expr>)> aux;
          aux = [&](List<expr> l) -> List<expr> {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return List<expr>::nil();
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return List<expr>::cons(d_a0.lit_map(f), aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }());
      }
    }

    __attribute__((pure)) List<unsigned int> literals() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        std::function<List<unsigned int>(List<expr>)> aux;
        aux = [&](List<expr> l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return d_a00.literals().app(aux(*(d_a10)));
          }
        };
        return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        std::function<List<unsigned int>(List<expr>)> aux;
        aux = [&](List<expr> l) -> List<unsigned int> {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return List<unsigned int>::nil();
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return d_a00.literals().app(aux(*(d_a10)));
          }
        };
        return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
      }
    }

    __attribute__((pure)) unsigned int expr_depth() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        return 0u;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return std::max(d_a0.expr_depth(), aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return std::max(d_a0.expr_depth(), aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }() + 1);
      }
    }

    __attribute__((pure)) unsigned int expr_size() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        return 1u;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (d_a0.expr_size() + aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }() + 1);
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return ([&]() {
          std::function<unsigned int(List<expr>)> aux;
          aux = [&](List<expr> l) -> unsigned int {
            if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
              return 0u;
            } else {
              const auto &[d_a0, d_a1] =
                  std::get<typename List<expr>::Cons>(l.v());
              return (d_a0.expr_size() + aux(*(d_a1)));
            }
          };
          return aux(clone_as_value<List<NestedInd::expr>>(d_a0));
        }() + 1);
      }
    }

    __attribute__((pure)) unsigned int eval() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        std::function<unsigned int(List<expr>)> sum_all;
        sum_all = [&](List<expr> l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 0u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return (d_a00.eval() + sum_all(*(d_a10)));
          }
        };
        return sum_all(clone_as_value<List<NestedInd::expr>>(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        std::function<unsigned int(List<expr>)> prod_all;
        prod_all = [&](List<expr> l) -> unsigned int {
          if (std::holds_alternative<typename List<expr>::Nil>(l.v())) {
            return 1u;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<expr>::Cons>(l.v());
            return (d_a00.eval() * prod_all(*(d_a10)));
          }
        };
        return prod_all(clone_as_value<List<NestedInd::expr>>(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<std::unique_ptr<expr>>> F1,
              MapsTo<T1, List<std::unique_ptr<expr>>> F2>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return f0(clone_as_value<List<NestedInd::expr>>(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return f1(clone_as_value<List<NestedInd::expr>>(d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, List<std::unique_ptr<expr>>> F1,
              MapsTo<T1, List<std::unique_ptr<expr>>> F2>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Lit>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Add>(_sv.v());
        return f0(clone_as_value<List<NestedInd::expr>>(d_a0));
      } else {
        const auto &[d_a0] = std::get<typename expr::Mul>(_sv.v());
        return f1(clone_as_value<List<NestedInd::expr>>(d_a0));
      }
    }
  };

  static inline const expr test_add = expr::add(List<expr>::cons(
      expr::lit(1u),
      List<expr>::cons(expr::lit(2u),
                       List<expr>::cons(expr::lit(3u), List<expr>::nil()))));
  static inline const expr test_mul = expr::mul(List<expr>::cons(
      expr::lit(2u),
      List<expr>::cons(expr::lit(3u),
                       List<expr>::cons(expr::lit(4u), List<expr>::nil()))));
  static inline const expr test_nested = expr::mul(List<expr>::cons(
      expr::add(List<expr>::cons(
          expr::lit(1u), List<expr>::cons(expr::lit(2u), List<expr>::nil()))),
      List<expr>::cons(expr::add(List<expr>::cons(
                           expr::lit(3u),
                           List<expr>::cons(expr::lit(4u), List<expr>::nil()))),
                       List<expr>::nil())));
  static inline const unsigned int test_eval_add = test_add.eval();
  static inline const unsigned int test_eval_mul = test_mul.eval();
  static inline const unsigned int test_eval_nested = test_nested.eval();
  static inline const unsigned int test_size_nested = test_nested.expr_size();
  static inline const unsigned int test_depth_nested = test_nested.expr_depth();
  static inline const List<unsigned int> test_literals = test_nested.literals();
  static inline const unsigned int test_doubled =
      test_nested.lit_map([](const unsigned int &n) { return (n * 2u); })
          .eval();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<
                                  std::pair<std::pair<std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>,
                                            unsigned int>,
                                  unsigned int>,
                              unsigned int>,
                          unsigned int>,
                      unsigned int>,
                  unsigned int>,
              unsigned int>,
          List<unsigned int>>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(
                                              std::make_pair(test_root_leaf,
                                                             test_root_small),
                                              test_children_leaf),
                                          test_children_small),
                                      test_children_bigger),
                                  test_eval_add),
                              test_eval_mul),
                          test_eval_nested),
                      test_size_nested),
                  test_depth_nested),
              test_literals),
          test_doubled);
};

#endif // INCLUDED_NESTED_IND
