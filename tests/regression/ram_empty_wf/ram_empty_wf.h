#ifndef INCLUDED_RAM_EMPTY_WF
#define INCLUDED_RAM_EMPTY_WF

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

struct ListDef {
  template <typename T1>
  __attribute__((pure)) static List<T1> repeat(const T1 x,
                                               const unsigned int &n);
};

struct RamEmptyWf {
  struct ram_reg {
    List<unsigned int> reg_main;
    List<unsigned int> reg_status;

    __attribute__((pure)) ram_reg *operator->() { return this; }

    __attribute__((pure)) const ram_reg *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ram_reg clone() const {
      return ram_reg{(*(this)).reg_main, (*(this)).reg_status};
    }
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    unsigned int chip_port;

    __attribute__((pure)) ram_chip *operator->() { return this; }

    __attribute__((pure)) const ram_chip *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ram_chip clone() const {
      return ram_chip{(*(this)).chip_regs, (*(this)).chip_port};
    }
  };

  struct ram_bank {
    List<ram_chip> bank_chips;

    __attribute__((pure)) ram_bank *operator->() { return this; }

    __attribute__((pure)) const ram_bank *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ram_bank clone() const {
      return ram_bank{(*(this)).bank_chips};
    }
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;

    __attribute__((pure)) ram_sel *operator->() { return this; }

    __attribute__((pure)) const ram_sel *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ram_sel clone() const {
      return ram_sel{(*(this)).sel_bank, (*(this)).sel_chip, (*(this)).sel_reg,
                     (*(this)).sel_char};
    }
  };

  static inline const ram_reg empty_reg =
      ram_reg{ListDef::template repeat<unsigned int>(0u, 16u),
              ListDef::template repeat<unsigned int>(0u, 4u)};
  static inline const ram_chip empty_chip =
      ram_chip{ListDef::template repeat<ram_reg>(empty_reg, 4u), 0u};
  static inline const ram_bank empty_bank =
      ram_bank{ListDef::template repeat<ram_chip>(empty_chip, 4u)};
  static inline const List<ram_bank> empty_ram =
      ListDef::template repeat<ram_bank>(empty_bank, 4u);
  static inline const ram_sel default_sel = ram_sel{0u, 0u, 0u, 0u};
  static inline const unsigned int default_bank_idx = default_sel.sel_bank;
};

template <typename T1>
__attribute__((pure)) List<T1> ListDef::repeat(const T1 x,
                                               const unsigned int &n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_EMPTY_WF
