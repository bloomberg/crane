#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

#include <memory>
#include <optional>
#include <stdexcept>
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
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      unsigned int d_n;
    };

    struct FS {
      unsigned int d_n;
      std::unique_ptr<fin> d_a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fin() {}

    explicit fin(FZ _v) : d_v_(std::move(_v)) {}

    explicit fin(FS _v) : d_v_(std::move(_v)) {}

    fin(const fin &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fin(fin &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) fin &operator=(const fin &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) fin &operator=(fin &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) fin clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<FZ>(_sv.v())) {
        const auto &[d_n] = std::get<FZ>(_sv.v());
        return fin(FZ{d_n});
      } else {
        const auto &[d_n, d_a1] = std::get<FS>(_sv.v());
        return fin(FS{d_n, clone_as_value<std::unique_ptr<fin>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static fin fz(unsigned int n) {
      return fin(FZ{std::move(n)});
    }

    __attribute__((pure)) static fin fs(unsigned int n, const fin &a1) {
      return fin(FS{std::move(n), std::make_unique<fin>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) fin *operator->() { return this; }

    __attribute__((pure)) const fin *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = fin(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int fin_to_nat(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return ((*(d_a1)).fin_to_nat(d_n) + 1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, fin, T1> F1>
    T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(_sv.v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return f0(d_n, *(d_a1), (*(d_a1)).template fin_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, fin, T1> F1>
    T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(_sv.v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return f0(d_n, *(d_a1), (*(d_a1)).template fin_rect<T1>(f, f0, d_n));
      }
    }
  };

  template <typename t_A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      unsigned int d_n;
      t_A d_a1;
      std::unique_ptr<vec<t_A>> d_a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : d_v_(_v) {}

    explicit vec(Vcons _v) : d_v_(std::move(_v)) {}

    vec(const vec<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    vec(vec<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) vec<t_A> &operator=(const vec<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) vec<t_A> &operator=(vec<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) vec<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Vnil>(_sv.v())) {
        return vec<t_A>(Vnil{});
      } else {
        const auto &[d_n, d_a1, d_a2] = std::get<Vcons>(_sv.v());
        return vec<t_A>(Vcons{d_n, clone_as_value<t_A>(d_a1),
                              clone_as_value<std::unique_ptr<vec<t_A>>>(d_a2)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) vec<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Vnil>(_sv.v())) {
        return vec<_CloneT0>(typename vec<_CloneT0>::Vnil{});
      } else {
        const auto &[d_n, d_a1, d_a2] = std::get<Vcons>(_sv.v());
        return vec<_CloneT0>(typename vec<_CloneT0>::Vcons{
            d_n, clone_as_value<_CloneT0>(d_a1),
            clone_as_value<std::unique_ptr<vec<_CloneT0>>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static vec<t_A> vnil() { return vec(Vnil{}); }

    __attribute__((pure)) static vec<t_A> vcons(unsigned int n, t_A a1,
                                                const vec<t_A> &a2) {
      return vec(Vcons{std::move(n), std::move(a1),
                       std::make_unique<vec<t_A>>(a2.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) vec<t_A> *operator->() { return this; }

    __attribute__((pure)) const vec<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = vec<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) vec<t_A> vec_tail(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return *(d_a2);
      }
    }

    t_A vec_head(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return d_a1;
      }
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    __attribute__((pure)) vec<T1> vec_map(const unsigned int &, F1 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return vec<T1>::vnil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return vec<T1>::vcons(d_n, f(d_a1),
                              (*(d_a2)).template vec_map<T1>(d_n, f));
      }
    }

    __attribute__((pure)) List<t_A> vec_to_list(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return List<t_A>::cons(d_a1, (*(d_a2)).vec_to_list(d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, t_A, vec<t_A>, T1> F1>
    T1 vec_rec(const T1 f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return f0(d_n, d_a1, *(d_a2),
                  (*(d_a2)).template vec_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, t_A, vec<t_A>, T1> F1>
    T1 vec_rect(const T1 f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return f0(d_n, d_a1, *(d_a2),
                  (*(d_a2)).template vec_rect<T1>(f, f0, d_n));
      }
    }
  };

  struct avail {
    // TYPES
    struct Present {
      unsigned int d_a0;
    };

    struct Absent {};

    using variant_t = std::variant<Present, Absent>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    avail() {}

    explicit avail(Present _v) : d_v_(std::move(_v)) {}

    explicit avail(Absent _v) : d_v_(_v) {}

    avail(const avail &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    avail(avail &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) avail &operator=(const avail &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) avail &operator=(avail &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) avail clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Present>(_sv.v())) {
        const auto &[d_a0] = std::get<Present>(_sv.v());
        return avail(Present{d_a0});
      } else {
        return avail(Absent{});
      }
    }

    // CREATORS
    __attribute__((pure)) static avail present(unsigned int a0) {
      return avail(Present{std::move(a0)});
    }

    constexpr static avail absent() { return avail(Absent{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) avail *operator->() { return this; }

    __attribute__((pure)) const avail *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = avail(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int get_present() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return d_a0;
      } else {
        throw std::logic_error("unreachable");
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rec(F0 &&f, const T1 f0, const bool &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rect(F0 &&f, const T1 f0, const bool &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }
  };

  static inline const unsigned int test_fin0 = fin::fz(2u).fin_to_nat(3u);
  static inline const unsigned int test_fin2 =
      fin::fs(2u, fin::fs(1u, fin::fz(0u))).fin_to_nat(3u);
  static inline const vec<unsigned int> my_vec = vec<unsigned int>::vcons(
      2u, 10u,
      vec<unsigned int>::vcons(
          1u, 20u,
          vec<unsigned int>::vcons(0u, 30u, vec<unsigned int>::vnil())));
  static inline const List<unsigned int> test_vec_list = my_vec.vec_to_list(3u);
  static inline const unsigned int test_vec_head = my_vec.vec_head(2u);
  static inline const List<unsigned int> test_vec_tail_list =
      my_vec.vec_tail(2u).vec_to_list(2u);
  static inline const List<unsigned int> test_vec_map =
      my_vec
          .template vec_map<unsigned int>(
              3u, [](const unsigned int &n) { return (n + 1u); })
          .vec_to_list(3u);
  static inline const unsigned int test_present =
      avail::present(42u).get_present();
};

#endif // INCLUDED_DEP_ELIM
