#ifndef INCLUDED_NO_MAPPING_EVENT_PROBE
#define INCLUDED_NO_MAPPING_EVENT_PROBE

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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
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
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
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

struct NoMappingEventProbe {
  struct reproE {
    // TYPES
    struct Hidden {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct Revealed {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<Hidden, Revealed>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    reproE() {}

    explicit reproE(Hidden _v) : d_v_(std::move(_v)) {}

    explicit reproE(Revealed _v) : d_v_(std::move(_v)) {}

    reproE(const reproE &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    reproE(reproE &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) reproE &operator=(const reproE &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) reproE &operator=(reproE &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) reproE clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Hidden>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Hidden>(_sv.v());
        return reproE(Hidden{d_a0, d_a1});
      } else {
        const auto &[d_a0, d_a1] = std::get<Revealed>(_sv.v());
        return reproE(Revealed{d_a0, d_a1});
      }
    }

    // CREATORS
    __attribute__((pure)) static reproE hidden(unsigned int a0,
                                               unsigned int a1) {
      return reproE(Hidden{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static reproE revealed(unsigned int a0,
                                                 unsigned int a1) {
      return reproE(Revealed{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) reproE *operator->() { return this; }

    __attribute__((pure)) const reproE *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = reproE(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 reproE_rect(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Hidden>(r.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(d_a0, d_a1);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F0,
            MapsTo<T1, unsigned int, unsigned int> F1>
  static T1 reproE_rec(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Hidden>(r.v());
      return f(d_a0, d_a1);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(d_a0, d_a1);
    }
  }

  static inline const unsigned int cell_size = 42u;
  static void draw_hidden_tile(unsigned int x, unsigned int y);
  static void draw_revealed_tile(unsigned int x, unsigned int y);
  static void loop(unsigned int x, unsigned int y, const List<bool> &cells);
};

#endif // INCLUDED_NO_MAPPING_EVENT_PROBE
