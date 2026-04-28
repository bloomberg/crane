#ifndef INCLUDED_RAM_WRITE
#define INCLUDED_RAM_WRITE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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

struct ListDef {
  template <typename T1>
  __attribute__((pure)) static List<T1> repeat(const T1 x,
                                               const unsigned int &n);
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct RamWrite {
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

    // ACCESSORS
    __attribute__((pure)) ram_reg clone() const {
      return ram_reg{(*(this)).reg_main.clone(), (*(this)).reg_status.clone()};
    }
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    unsigned int chip_port;

    // ACCESSORS
    __attribute__((pure)) ram_chip clone() const {
      return ram_chip{(*(this)).chip_regs.clone(), (*(this)).chip_port};
    }
  };

  struct ram_bank {
    List<ram_chip> bank_chips;

    // ACCESSORS
    __attribute__((pure)) ram_bank clone() const {
      return ram_bank{(*(this)).bank_chips.clone()};
    }
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;

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

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).state_regs.clone(),  (*(this)).state_acc,
                   (*(this)).state_carry,         (*(this)).state_pc,
                   (*(this)).state_stack.clone(), (*(this)).state_ram.clone(),
                   (*(this)).state_sel.clone(),   (*(this)).state_rom.clone()};
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
  static inline const state init_state =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            0u,
            false,
            0u,
            List<unsigned int>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<unsigned int>(0u, 8u)};
  __attribute__((pure)) static unsigned int get_main(const ram_reg &rg,
                                                     const unsigned int &i);
  __attribute__((pure)) static ram_reg upd_main_in_reg(const ram_reg &rg,
                                                       const unsigned int &i,
                                                       const unsigned int &v);
  __attribute__((pure)) static ram_reg upd_stat_in_reg(const ram_reg &rg,
                                                       const unsigned int &i,
                                                       const unsigned int &v);
  __attribute__((pure)) static ram_reg get_regRAM(const ram_chip &ch,
                                                  const unsigned int &r);
  __attribute__((pure)) static ram_chip
  upd_reg_in_chip(const ram_chip &ch, const unsigned int &r, const ram_reg &rg);
  __attribute__((pure)) static ram_chip get_chip(const ram_bank &bk,
                                                 const unsigned int &c);
  __attribute__((pure)) static ram_bank upd_chip_in_bank(const ram_bank &bk,
                                                         const unsigned int &c,
                                                         const ram_chip &ch);
  __attribute__((pure)) static ram_bank
  get_bank_from_sys(const List<ram_bank> &sys, const unsigned int &b);
  __attribute__((pure)) static List<ram_bank>
  upd_bank_in_sys(const state &s, const unsigned int &b, const ram_bank &bk);
  __attribute__((pure)) static ram_bank current_bank(const state &s);
  __attribute__((pure)) static ram_chip current_chip(const state &s);
  __attribute__((pure)) static ram_reg current_reg(const state &s);
  __attribute__((pure)) static unsigned int ram_read_main(const state &s);
  __attribute__((pure)) static List<ram_bank>
  ram_write_main_sys(const state &s, const unsigned int &v);
  __attribute__((pure)) static List<ram_bank>
  ram_write_status_sys(const state &s, const unsigned int &idx,
                       const unsigned int &v);
  static inline const unsigned int write_bank_count =
      ram_write_main_sys(init_state, 12u).length();
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

template <typename T1>
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_RAM_WRITE
