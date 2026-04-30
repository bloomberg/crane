#ifndef INCLUDED_RAM_OPS
#define INCLUDED_RAM_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct RamOps {
  struct ram_reg_main {
    List<unsigned int> reg_main;

    // ACCESSORS
    ram_reg_main clone() const {
      return ram_reg_main{(*(this)).reg_main.clone()};
    }
  };

  struct ram_chip_main {
    List<ram_reg_main> chip_regs_main;

    // ACCESSORS
    ram_chip_main clone() const {
      return ram_chip_main{(*(this)).chip_regs_main.clone()};
    }
  };

  struct ram_bank_main {
    List<ram_chip_main> bank_chips_main;

    // ACCESSORS
    ram_bank_main clone() const {
      return ram_bank_main{(*(this)).bank_chips_main.clone()};
    }
  };

  struct state_main {
    List<ram_bank_main> ram_sys_main;
    unsigned int cur_bank_main;
    unsigned int sel_chip_main;
    unsigned int sel_reg_main;
    unsigned int sel_char_main;

    // ACCESSORS
    state_main clone() const {
      return state_main{(*(this)).ram_sys_main.clone(), (*(this)).cur_bank_main,
                        (*(this)).sel_chip_main, (*(this)).sel_reg_main,
                        (*(this)).sel_char_main};
    }
  };

  template <typename T1>
  static List<T1> update_nth_main(const unsigned int &n, const T1 x,
                                  const List<T1> &l) {
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
        return List<T1>::cons(d_a00, update_nth_main<T1>(n_, x, *(d_a10)));
      }
    }
  }

  static ram_bank_main get_bank_main(const state_main &s,
                                     const unsigned int &b);
  static ram_chip_main get_chip_main(const ram_bank_main &bk,
                                     const unsigned int &c);
  static ram_reg_main get_reg_main(const ram_chip_main &ch,
                                   const unsigned int &r);
  static ram_reg_main upd_main_in_reg(const ram_reg_main &rg,
                                      const unsigned int &i,
                                      const unsigned int &v);
  static ram_chip_main upd_reg_in_chip_main(const ram_chip_main &ch,
                                            const unsigned int &r,
                                            const ram_reg_main &rg);
  static ram_bank_main upd_chip_in_bank_main(const ram_bank_main &bk,
                                             const unsigned int &c,
                                             const ram_chip_main &ch);
  static List<ram_bank_main> upd_bank_in_sys_main(const state_main &s,
                                                  const unsigned int &b,
                                                  const ram_bank_main &bk);
  static List<ram_bank_main> ram_write_main_sys(const state_main &s,
                                                const unsigned int &v);
  static inline const unsigned int test_main_write_chain = []() {
    ram_reg_main rg0 = ram_reg_main{List<unsigned int>::cons(
        0u, List<unsigned int>::cons(
                0u, List<unsigned int>::cons(0u, List<unsigned int>::nil())))};
    ram_chip_main ch0 =
        ram_chip_main{List<ram_reg_main>::cons(rg0, List<ram_reg_main>::nil())};
    ram_bank_main bk0 = ram_bank_main{
        List<ram_chip_main>::cons(ch0, List<ram_chip_main>::nil())};
    state_main s =
        state_main{List<ram_bank_main>::cons(bk0, List<ram_bank_main>::nil()),
                   0u, 0u, 0u, 1u};
    List<ram_bank_main> sys_ = ram_write_main_sys(std::move(s), 19u);
    ram_bank_main bk_ = ListDef::template nth<ram_bank_main>(
        0u, std::move(sys_), ram_bank_main{List<ram_chip_main>::nil()});
    ram_chip_main ch_ = ListDef::template nth<ram_chip_main>(
        0u, std::move(bk_).bank_chips_main,
        ram_chip_main{List<ram_reg_main>::nil()});
    ram_reg_main rg_ = ListDef::template nth<ram_reg_main>(
        0u, std::move(ch_).chip_regs_main,
        ram_reg_main{List<unsigned int>::nil()});
    return ListDef::template nth<unsigned int>(1u, std::move(rg_).reg_main, 0u);
  }();

  struct chip_port {
    unsigned int chip_port_val;

    // ACCESSORS
    chip_port clone() const { return chip_port{(*(this)).chip_port_val}; }
  };

  struct bank_port {
    List<chip_port> bank_chips_port;

    // ACCESSORS
    bank_port clone() const {
      return bank_port{(*(this)).bank_chips_port.clone()};
    }
  };

  struct state_port {
    List<bank_port> ram_sys_port;
    unsigned int cur_bank_port;
    unsigned int sel_chip_port;

    // ACCESSORS
    state_port clone() const {
      return state_port{(*(this)).ram_sys_port.clone(), (*(this)).cur_bank_port,
                        (*(this)).sel_chip_port};
    }
  };

  template <typename T1>
  static List<T1> update_nth_port(const unsigned int &n, const T1 x,
                                  const List<T1> &l) {
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
        return List<T1>::cons(d_a00, update_nth_port<T1>(n_, x, *(d_a10)));
      }
    }
  }

  static bank_port get_bank_port(const state_port &s, const unsigned int &b);
  static chip_port get_chip_port(const bank_port &bk, const unsigned int &c);
  static chip_port upd_port_in_chip(const chip_port &_x, const unsigned int &v);
  static bank_port upd_chip_in_bank_port(const bank_port &bk,
                                         const unsigned int &c,
                                         const chip_port &ch);
  static List<bank_port> upd_bank_in_sys_port(const state_port &s,
                                              const unsigned int &b,
                                              const bank_port &bk);
  static List<bank_port> ram_write_port_sys(const state_port &s,
                                            const unsigned int &v);
  static inline const unsigned int test_port_write_chain = []() {
    chip_port ch0 = chip_port{0u};
    bank_port bk0 =
        bank_port{List<chip_port>::cons(ch0, List<chip_port>::nil())};
    state_port s =
        state_port{List<bank_port>::cons(bk0, List<bank_port>::nil()), 0u, 0u};
    List<bank_port> sys_ = ram_write_port_sys(std::move(s), 17u);
    bank_port bk_ = ListDef::template nth<bank_port>(
        0u, std::move(sys_), bank_port{List<chip_port>::nil()});
    chip_port ch_ = ListDef::template nth<chip_port>(
        0u, std::move(bk_).bank_chips_port, chip_port{0u});
    return std::move(ch_).chip_port_val;
  }();

  struct ram_reg_status {
    List<unsigned int> reg_status;

    // ACCESSORS
    ram_reg_status clone() const {
      return ram_reg_status{(*(this)).reg_status.clone()};
    }
  };

  struct ram_chip_status {
    List<ram_reg_status> chip_regs_status;

    // ACCESSORS
    ram_chip_status clone() const {
      return ram_chip_status{(*(this)).chip_regs_status.clone()};
    }
  };

  struct ram_bank_status {
    List<ram_chip_status> bank_chips_status;

    // ACCESSORS
    ram_bank_status clone() const {
      return ram_bank_status{(*(this)).bank_chips_status.clone()};
    }
  };

  struct state_status {
    List<ram_bank_status> ram_sys_status;
    unsigned int cur_bank_status;
    unsigned int sel_chip_status;
    unsigned int sel_reg_status;

    // ACCESSORS
    state_status clone() const {
      return state_status{(*(this)).ram_sys_status.clone(),
                          (*(this)).cur_bank_status, (*(this)).sel_chip_status,
                          (*(this)).sel_reg_status};
    }
  };

  template <typename T1>
  static List<T1> update_nth_status(const unsigned int &n, const T1 x,
                                    const List<T1> &l) {
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
        return List<T1>::cons(d_a00, update_nth_status<T1>(n_, x, *(d_a10)));
      }
    }
  }

  static ram_bank_status get_bank_status(const state_status &s,
                                         const unsigned int &b);
  static ram_chip_status get_chip_status(const ram_bank_status &bk,
                                         const unsigned int &c);
  static ram_reg_status get_reg_status(const ram_chip_status &ch,
                                       const unsigned int &r);
  static ram_reg_status upd_status_in_reg(const ram_reg_status &rg,
                                          const unsigned int &i,
                                          const unsigned int &v);
  static ram_chip_status upd_reg_in_chip_status(const ram_chip_status &ch,
                                                const unsigned int &r,
                                                const ram_reg_status &rg);
  static ram_bank_status upd_chip_in_bank_status(const ram_bank_status &bk,
                                                 const unsigned int &c,
                                                 const ram_chip_status &ch);
  static List<ram_bank_status>
  upd_bank_in_sys_status(const state_status &s, const unsigned int &b,
                         const ram_bank_status &bk);
  static List<ram_bank_status> ram_write_status_sys(const state_status &s,
                                                    const unsigned int &idx,
                                                    const unsigned int &v);
  static inline const unsigned int test_status_write_chain = []() {
    ram_reg_status rg0 = ram_reg_status{List<unsigned int>::cons(
        0u, List<unsigned int>::cons(
                0u, List<unsigned int>::cons(
                        0u, List<unsigned int>::cons(
                                0u, List<unsigned int>::nil()))))};
    ram_chip_status ch0 = ram_chip_status{
        List<ram_reg_status>::cons(rg0, List<ram_reg_status>::nil())};
    ram_bank_status bk0 = ram_bank_status{
        List<ram_chip_status>::cons(ch0, List<ram_chip_status>::nil())};
    state_status s = state_status{
        List<ram_bank_status>::cons(bk0, List<ram_bank_status>::nil()), 0u, 0u,
        0u};
    List<ram_bank_status> sys_ = ram_write_status_sys(std::move(s), 2u, 25u);
    ram_bank_status bk_ = ListDef::template nth<ram_bank_status>(
        0u, std::move(sys_), ram_bank_status{List<ram_chip_status>::nil()});
    ram_chip_status ch_ = ListDef::template nth<ram_chip_status>(
        0u, std::move(bk_).bank_chips_status,
        ram_chip_status{List<ram_reg_status>::nil()});
    ram_reg_status rg_ = ListDef::template nth<ram_reg_status>(
        0u, std::move(ch_).chip_regs_status,
        ram_reg_status{List<unsigned int>::nil()});
    return ListDef::template nth<unsigned int>(2u, std::move(rg_).reg_status,
                                               0u);
  }();

  struct ram_reg_sel {
    List<unsigned int> reg_main_sel;
    List<unsigned int> reg_status_sel;

    // ACCESSORS
    ram_reg_sel clone() const {
      return ram_reg_sel{(*(this)).reg_main_sel.clone(),
                         (*(this)).reg_status_sel.clone()};
    }
  };

  struct ram_chip_sel {
    List<ram_reg_sel> chip_regs_sel;
    unsigned int chip_port_sel;

    // ACCESSORS
    ram_chip_sel clone() const {
      return ram_chip_sel{(*(this)).chip_regs_sel.clone(),
                          (*(this)).chip_port_sel};
    }
  };

  struct ram_bank_sel {
    List<ram_chip_sel> bank_chips_sel;

    // ACCESSORS
    ram_bank_sel clone() const {
      return ram_bank_sel{(*(this)).bank_chips_sel.clone()};
    }
  };

  struct ram_sel {
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;

    // ACCESSORS
    ram_sel clone() const {
      return ram_sel{(*(this)).sel_chip, (*(this)).sel_reg, (*(this)).sel_char};
    }
  };

  struct state_sel {
    List<ram_bank_sel> ram_sys_sel;
    unsigned int cur_bank_sel;
    ram_sel sel_ram;

    // ACCESSORS
    state_sel clone() const {
      return state_sel{(*(this)).ram_sys_sel.clone(), (*(this)).cur_bank_sel,
                       (*(this)).sel_ram.clone()};
    }
  };

  static inline const ram_reg_sel empty_reg_sel =
      ram_reg_sel{List<unsigned int>::nil(), List<unsigned int>::nil()};
  static inline const ram_chip_sel empty_chip_sel =
      ram_chip_sel{List<ram_reg_sel>::nil(), 0u};
  static inline const ram_bank_sel empty_bank_sel =
      ram_bank_sel{List<ram_chip_sel>::nil()};
  static ram_bank_sel get_bank_sel(const state_sel &s, const unsigned int &b);
  static ram_chip_sel get_chip_sel(const ram_bank_sel &bk,
                                   const unsigned int &c);
  static ram_reg_sel get_regRAM(const ram_chip_sel &ch, const unsigned int &r);
  static unsigned int get_main_sel(const ram_reg_sel &rg,
                                   const unsigned int &i);
  static unsigned int ram_read_main(const state_sel &s);
  static inline const ram_reg_sel sample_reg_sel = ram_reg_sel{
      List<unsigned int>::cons(
          5u, List<unsigned int>::cons(
                  6u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::nil())))),
      List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::nil()))))};
  static inline const ram_chip_sel sample_chip_sel = ram_chip_sel{
      List<ram_reg_sel>::cons(sample_reg_sel, List<ram_reg_sel>::nil()), 3u};
  static inline const ram_bank_sel sample_bank_sel = ram_bank_sel{
      List<ram_chip_sel>::cons(sample_chip_sel, List<ram_chip_sel>::nil())};
  static inline const ram_sel sample_sel = ram_sel{0u, 0u, 2u};
  static inline const state_sel sample_state_sel = state_sel{
      List<ram_bank_sel>::cons(sample_bank_sel, List<ram_bank_sel>::nil()), 0u,
      sample_sel};
  static inline const unsigned int test_read_main_selector =
      ram_read_main(sample_state_sel);

  struct ram_reg_nested {
    List<unsigned int> reg_main_nested;
    List<unsigned int> reg_status_nested;

    // ACCESSORS
    ram_reg_nested clone() const {
      return ram_reg_nested{(*(this)).reg_main_nested.clone(),
                            (*(this)).reg_status_nested.clone()};
    }
  };

  struct ram_chip_nested {
    List<ram_reg_nested> chip_regs_nested;
    unsigned int chip_port_nested;

    // ACCESSORS
    ram_chip_nested clone() const {
      return ram_chip_nested{(*(this)).chip_regs_nested.clone(),
                             (*(this)).chip_port_nested};
    }
  };

  struct ram_bank_nested {
    List<ram_chip_nested> bank_chips_nested;

    // ACCESSORS
    ram_bank_nested clone() const {
      return ram_bank_nested{(*(this)).bank_chips_nested.clone()};
    }
  };

  struct ram_sel_nested {
    unsigned int sel_chip_nested;
    unsigned int sel_reg_nested;
    unsigned int sel_char_nested;

    // ACCESSORS
    ram_sel_nested clone() const {
      return ram_sel_nested{(*(this)).sel_chip_nested, (*(this)).sel_reg_nested,
                            (*(this)).sel_char_nested};
    }
  };

  struct state_nested {
    List<ram_bank_nested> ram_sys_nested;
    unsigned int cur_bank_nested;
    ram_sel_nested sel_ram_nested;

    // ACCESSORS
    state_nested clone() const {
      return state_nested{(*(this)).ram_sys_nested.clone(),
                          (*(this)).cur_bank_nested,
                          (*(this)).sel_ram_nested.clone()};
    }
  };

  static inline const ram_reg_nested empty_reg_nested =
      ram_reg_nested{List<unsigned int>::nil(), List<unsigned int>::nil()};
  static inline const ram_chip_nested empty_chip_nested =
      ram_chip_nested{List<ram_reg_nested>::nil(), 0u};
  static inline const ram_bank_nested empty_bank_nested =
      ram_bank_nested{List<ram_chip_nested>::nil()};
  static ram_bank_nested get_bank_nested(const state_nested &s,
                                         const unsigned int &b);
  static ram_chip_nested get_chip_nested(const ram_bank_nested &bk,
                                         const unsigned int &c);
  static ram_reg_nested get_regRAM_nested(const ram_chip_nested &ch,
                                          const unsigned int &r);
  static unsigned int get_main_nested(const ram_reg_nested &rg,
                                      const unsigned int &i);
  static unsigned int ram_read_main_nested(const state_nested &s);
  static inline const ram_reg_nested sample_reg_nested = ram_reg_nested{
      List<unsigned int>::cons(
          5u, List<unsigned int>::cons(
                  6u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  8u, List<unsigned int>::nil())))),
      List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::nil()))))};
  static inline const ram_chip_nested sample_chip_nested =
      ram_chip_nested{List<ram_reg_nested>::cons(sample_reg_nested,
                                                 List<ram_reg_nested>::nil()),
                      3u};
  static inline const ram_bank_nested sample_bank_nested =
      ram_bank_nested{List<ram_chip_nested>::cons(
          sample_chip_nested, List<ram_chip_nested>::nil())};
  static inline const ram_sel_nested sample_sel_nested =
      ram_sel_nested{0u, 0u, 2u};
  static inline const state_nested sample_state_nested =
      state_nested{List<ram_bank_nested>::cons(sample_bank_nested,
                                               List<ram_bank_nested>::nil()),
                   0u, sample_sel_nested};
  static inline const unsigned int test_read_nested =
      ram_read_main_nested(sample_state_nested);

  template <typename T1>
  static List<T1> update_nth_frame(const unsigned int &n, const T1 x,
                                   const List<T1> &l) {
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
        return List<T1>::cons(d_a00, update_nth_frame<T1>(n_, x, *(d_a10)));
      }
    }
  }

  using reg_frame = List<unsigned int>;
  using chip_frame = List<reg_frame>;
  using bank_frame = List<chip_frame>;
  static reg_frame upd_main_in_reg_frame(const List<unsigned int> &rg,
                                         const unsigned int &i,
                                         const unsigned int &v);
  static chip_frame upd_reg_in_chip_frame(const List<List<unsigned int>> &ch,
                                          const unsigned int &r,
                                          const List<unsigned int> &rg);
  static bank_frame
  upd_chip_in_bank_frame(const List<List<List<unsigned int>>> &bk,
                         const unsigned int &c,
                         const List<List<unsigned int>> &ch);
  static inline const bank_frame sample_bank_frame =
      List<List<List<unsigned int>>>::cons(
          List<List<unsigned int>>::cons(
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(
                          2u, List<unsigned int>::cons(
                                  3u, List<unsigned int>::nil()))),
              List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(
                      4u, List<unsigned int>::cons(
                              5u, List<unsigned int>::cons(
                                      6u, List<unsigned int>::nil()))),
                  List<List<unsigned int>>::nil())),
          List<List<List<unsigned int>>>::cons(
              List<List<unsigned int>>::cons(
                  List<unsigned int>::cons(
                      7u, List<unsigned int>::cons(
                              8u, List<unsigned int>::cons(
                                      9u, List<unsigned int>::nil()))),
                  List<List<unsigned int>>::cons(
                      List<unsigned int>::cons(
                          10u, List<unsigned int>::cons(
                                   11u, List<unsigned int>::cons(
                                            12u, List<unsigned int>::nil()))),
                      List<List<unsigned int>>::nil())),
              List<List<List<unsigned int>>>::nil()));
  static inline const bank_frame updated_bank_frame = []() {
    List<List<unsigned int>> ch = ListDef::template nth<chip_frame>(
        0u, sample_bank_frame, List<List<unsigned int>>::nil());
    List<unsigned int> rg =
        ListDef::template nth<reg_frame>(1u, ch, List<unsigned int>::nil());
    List<unsigned int> rg_ = upd_main_in_reg_frame(std::move(rg), 2u, 99u);
    List<List<unsigned int>> ch_ =
        upd_reg_in_chip_frame(std::move(ch), 1u, std::move(rg_));
    return upd_chip_in_bank_frame(sample_bank_frame, 0u, std::move(ch_));
  }();
  static inline const bool test_write_frame_different_chip =
      ListDef::template nth<unsigned int>(
          2u,
          ListDef::template nth<reg_frame>(
              0u,
              ListDef::template nth<chip_frame>(
                  1u, updated_bank_frame, List<List<unsigned int>>::nil()),
              List<unsigned int>::nil()),
          0u) == 7u;

  template <typename T1>
  static List<T1> update_nth_preserve(const unsigned int &n, const T1 x,
                                      const List<T1> &l) {
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
        return List<T1>::cons(d_a00, update_nth_preserve<T1>(n_, x, *(d_a10)));
      }
    }
  }

  struct state_preserve {
    List<unsigned int> ram_sys_preserve;
    unsigned int cur_bank_preserve;

    // ACCESSORS
    state_preserve clone() const {
      return state_preserve{(*(this)).ram_sys_preserve.clone(),
                            (*(this)).cur_bank_preserve};
    }
  };

  static List<unsigned int> ram_write_main_sys_preserve(const state_preserve &s,
                                                        const unsigned int &v);
  static state_preserve execute_write(const state_preserve &s,
                                      const unsigned int &v);
  static inline const state_preserve sample_preserve = state_preserve{
      List<unsigned int>::cons(
          10u, List<unsigned int>::cons(
                   20u, List<unsigned int>::cons(
                            30u, List<unsigned int>::cons(
                                     40u, List<unsigned int>::nil())))),
      1u};
  static inline const bool test_write_main_preserves_other_bank =
      ListDef::template nth<unsigned int>(
          3u, execute_write(sample_preserve, 99u).ram_sys_preserve, 0u) == 40u;
  static bool ram_addr_disjointb(const unsigned int &b1, const unsigned int &c1,
                                 const unsigned int &r1, const unsigned int &i1,
                                 const unsigned int &b2, const unsigned int &c2,
                                 const unsigned int &r2,
                                 const unsigned int &i2);
  static inline const unsigned int test_addr_disjoint_bool =
      ((ram_addr_disjointb(0u, 1u, 2u, 3u, 0u, 1u, 2u, 3u) ? 1u : 0u) +
       (ram_addr_disjointb(0u, 1u, 2u, 3u, 0u, 1u, 2u, 4u) ? 1u : 0u));

  struct reg_nested_bank {
    List<unsigned int> status_;

    // ACCESSORS
    reg_nested_bank clone() const {
      return reg_nested_bank{(*(this)).status_.clone()};
    }
  };

  struct chip_nested_bank {
    List<reg_nested_bank> regs_;

    // ACCESSORS
    chip_nested_bank clone() const {
      return chip_nested_bank{(*(this)).regs_.clone()};
    }
  };

  struct bank_nested_bank {
    List<chip_nested_bank> chips_;

    // ACCESSORS
    bank_nested_bank clone() const {
      return bank_nested_bank{(*(this)).chips_.clone()};
    }
  };

  struct state_nested_bank {
    List<bank_nested_bank> banks_;

    // ACCESSORS
    state_nested_bank clone() const {
      return state_nested_bank{(*(this)).banks_.clone()};
    }
  };

  template <typename T1>
  static List<T1> update_nth_nested_bank(const unsigned int &n, const T1 x,
                                         const List<T1> &l) {
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
        return List<T1>::cons(d_a00,
                              update_nth_nested_bank<T1>(n_, x, *(d_a10)));
      }
    }
  }

  static bank_nested_bank get_bank0(const state_nested_bank &s);
  static chip_nested_bank get_chip0(const bank_nested_bank &b);
  static reg_nested_bank get_reg0(const chip_nested_bank &c);
  static state_nested_bank write_status0(const state_nested_bank &s,
                                         const unsigned int &v);
  static unsigned int read_status0(const state_nested_bank &s);
  static inline const state_nested_bank sample_nested_bank =
      state_nested_bank{List<bank_nested_bank>::cons(
          bank_nested_bank{List<chip_nested_bank>::cons(
              chip_nested_bank{List<reg_nested_bank>::cons(
                  reg_nested_bank{List<unsigned int>::cons(
                      3u,
                      List<unsigned int>::cons(4u, List<unsigned int>::nil()))},
                  List<reg_nested_bank>::nil())},
              List<chip_nested_bank>::nil())},
          List<bank_nested_bank>::nil())};
  static inline const unsigned int test_nested_bank_status_write =
      read_status0(write_status0(sample_nested_bank, 7u));
  enum class Item { e_S_, e_S_0 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const Item i) {
    switch (i) {
    case Item::e_S_: {
      return f;
    }
    case Item::e_S_0: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const Item i) {
    switch (i) {
    case Item::e_S_: {
      return f;
    }
    case Item::e_S_0: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static unsigned int score(const Item x);
  static inline const unsigned int test_accessor_namespace =
      (score(Item::e_S_) + score(Item::e_S_0));
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<std::pair<std::pair<std::pair<unsigned int,
                                                              unsigned int>,
                                                    unsigned int>,
                                          unsigned int>,
                                unsigned int>,
                      unsigned int>,
                  bool>,
              bool>,
          unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(test_main_write_chain,
                                                     test_port_write_chain),
                                      test_status_write_chain),
                                  test_read_main_selector),
                              test_read_nested),
                          test_addr_disjoint_bool),
                      test_write_frame_different_chip),
                  test_write_main_preserves_other_bank),
              test_nested_bank_status_write),
          test_accessor_namespace);
};

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

#endif // INCLUDED_RAM_OPS
