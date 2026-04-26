#ifndef INCLUDED_RAM_BAD_STATE
#define INCLUDED_RAM_BAD_STATE

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

struct RamBadState {
  template <typename T1>
  __attribute__((pure)) static List<T1>
  update_nth(const unsigned int &n, const T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *(d_a1));
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, *(d_a10)));
      }
    }
  }

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

  struct state {
    List<unsigned int> state_regs;
    unsigned int state_acc;
    bool state_carry;
    unsigned int state_pc;
    List<unsigned int> state_stack;
    List<ram_bank> state_ram;
    ram_sel state_sel;
    List<unsigned int> state_rom;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).state_regs,  (*(this)).state_acc,
                   (*(this)).state_carry, (*(this)).state_pc,
                   (*(this)).state_stack, (*(this)).state_ram,
                   (*(this)).state_sel,   (*(this)).state_rom};
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
  static inline const state bad_state_acc_overflow =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            16u,
            false,
            0u,
            List<unsigned int>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<unsigned int>(0u, 8u)};
  static inline const state bad_state_pc_overflow =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            0u,
            false,
            4096u,
            List<unsigned int>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<unsigned int>(0u, 8u)};
  static inline const state bad_state_stack_overflow =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            0u,
            false,
            0u,
            List<unsigned int>::cons(
                0u, List<unsigned int>::cons(
                        1u, List<unsigned int>::cons(
                                2u, List<unsigned int>::cons(
                                        3u, List<unsigned int>::nil())))),
            empty_ram,
            default_sel,
            ListDef::template repeat<unsigned int>(0u, 8u)};
  static inline const state bad_state_wrong_reg_count =
      state{ListDef::template repeat<unsigned int>(0u, 15u),
            0u,
            false,
            0u,
            List<unsigned int>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<unsigned int>(0u, 8u)};
  static inline const unsigned int overflow_acc =
      bad_state_acc_overflow.state_acc;
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

#endif // INCLUDED_RAM_BAD_STATE
