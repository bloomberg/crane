#ifndef INCLUDED_RAM_OPS
#define INCLUDED_RAM_OPS

#include <memory>
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
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct RamOps {
  struct ram_reg_main {
    List<uint64_t> reg_main;

    // ACCESSORS
    ram_reg_main clone() const {
      return ram_reg_main{(*this).reg_main.clone()};
    }
  };

  struct ram_chip_main {
    List<ram_reg_main> chip_regs_main;

    // ACCESSORS
    ram_chip_main clone() const {
      return ram_chip_main{(*this).chip_regs_main.clone()};
    }
  };

  struct ram_bank_main {
    List<ram_chip_main> bank_chips_main;

    // ACCESSORS
    ram_bank_main clone() const {
      return ram_bank_main{(*this).bank_chips_main.clone()};
    }
  };

  struct state_main {
    List<ram_bank_main> ram_sys_main;
    uint64_t cur_bank_main;
    uint64_t sel_chip_main;
    uint64_t sel_reg_main;
    uint64_t sel_char_main;

    // ACCESSORS
    state_main clone() const {
      return state_main{(*this).ram_sys_main.clone(), (*this).cur_bank_main,
                        (*this).sel_chip_main, (*this).sel_reg_main,
                        (*this).sel_char_main};
    }
  };

  template <typename T1>
  static List<T1> update_nth_main(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_main<T1>(n_, x, *a10));
      }
    }
  }

  static ram_bank_main get_bank_main(const state_main &s, uint64_t b);
  static ram_chip_main get_chip_main(const ram_bank_main &bk, uint64_t c);
  static ram_reg_main get_reg_main(const ram_chip_main &ch, uint64_t r);
  static ram_reg_main upd_main_in_reg(const ram_reg_main &rg, uint64_t i,
                                      uint64_t v);
  static ram_chip_main upd_reg_in_chip_main(const ram_chip_main &ch, uint64_t r,
                                            const ram_reg_main &rg);
  static ram_bank_main upd_chip_in_bank_main(const ram_bank_main &bk,
                                             uint64_t c,
                                             const ram_chip_main &ch);
  static List<ram_bank_main> upd_bank_in_sys_main(const state_main &s,
                                                  uint64_t b,
                                                  const ram_bank_main &bk);
  static List<ram_bank_main> ram_write_main_sys(const state_main &s,
                                                uint64_t v);
  static inline const uint64_t test_main_write_chain = []() {
    ram_reg_main rg0 = ram_reg_main{List<uint64_t>::cons(
        UINT64_C(0),
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil())))};
    ram_chip_main ch0 =
        ram_chip_main{List<ram_reg_main>::cons(rg0, List<ram_reg_main>::nil())};
    ram_bank_main bk0 = ram_bank_main{
        List<ram_chip_main>::cons(ch0, List<ram_chip_main>::nil())};
    state_main s =
        state_main{List<ram_bank_main>::cons(bk0, List<ram_bank_main>::nil()),
                   UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(1)};
    List<ram_bank_main> sys_ = ram_write_main_sys(std::move(s), UINT64_C(19));
    ram_bank_main bk_ = ListDef::template nth<ram_bank_main>(
        UINT64_C(0), std::move(sys_),
        ram_bank_main{List<ram_chip_main>::nil()});
    ram_chip_main ch_ = ListDef::template nth<ram_chip_main>(
        UINT64_C(0), std::move(bk_).bank_chips_main,
        ram_chip_main{List<ram_reg_main>::nil()});
    ram_reg_main rg_ = ListDef::template nth<ram_reg_main>(
        UINT64_C(0), std::move(ch_).chip_regs_main,
        ram_reg_main{List<uint64_t>::nil()});
    return ListDef::template nth<uint64_t>(UINT64_C(1), std::move(rg_).reg_main,
                                           UINT64_C(0));
  }();

  struct chip_port {
    uint64_t chip_port_val;

    // ACCESSORS
    chip_port clone() const { return chip_port{(*this).chip_port_val}; }
  };

  struct bank_port {
    List<chip_port> bank_chips_port;

    // ACCESSORS
    bank_port clone() const {
      return bank_port{(*this).bank_chips_port.clone()};
    }
  };

  struct state_port {
    List<bank_port> ram_sys_port;
    uint64_t cur_bank_port;
    uint64_t sel_chip_port;

    // ACCESSORS
    state_port clone() const {
      return state_port{(*this).ram_sys_port.clone(), (*this).cur_bank_port,
                        (*this).sel_chip_port};
    }
  };

  template <typename T1>
  static List<T1> update_nth_port(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_port<T1>(n_, x, *a10));
      }
    }
  }

  static bank_port get_bank_port(const state_port &s, uint64_t b);
  static chip_port get_chip_port(const bank_port &bk, uint64_t c);
  static chip_port upd_port_in_chip(const chip_port &_x, uint64_t v);
  static bank_port upd_chip_in_bank_port(const bank_port &bk, uint64_t c,
                                         const chip_port &ch);
  static List<bank_port> upd_bank_in_sys_port(const state_port &s, uint64_t b,
                                              const bank_port &bk);
  static List<bank_port> ram_write_port_sys(const state_port &s, uint64_t v);
  static inline const uint64_t test_port_write_chain = []() {
    chip_port ch0 = chip_port{UINT64_C(0)};
    bank_port bk0 =
        bank_port{List<chip_port>::cons(ch0, List<chip_port>::nil())};
    state_port s =
        state_port{List<bank_port>::cons(bk0, List<bank_port>::nil()),
                   UINT64_C(0), UINT64_C(0)};
    List<bank_port> sys_ = ram_write_port_sys(std::move(s), UINT64_C(17));
    bank_port bk_ = ListDef::template nth<bank_port>(
        UINT64_C(0), std::move(sys_), bank_port{List<chip_port>::nil()});
    chip_port ch_ = ListDef::template nth<chip_port>(
        UINT64_C(0), std::move(bk_).bank_chips_port, chip_port{UINT64_C(0)});
    return std::move(ch_).chip_port_val;
  }();

  struct ram_reg_status {
    List<uint64_t> reg_status;

    // ACCESSORS
    ram_reg_status clone() const {
      return ram_reg_status{(*this).reg_status.clone()};
    }
  };

  struct ram_chip_status {
    List<ram_reg_status> chip_regs_status;

    // ACCESSORS
    ram_chip_status clone() const {
      return ram_chip_status{(*this).chip_regs_status.clone()};
    }
  };

  struct ram_bank_status {
    List<ram_chip_status> bank_chips_status;

    // ACCESSORS
    ram_bank_status clone() const {
      return ram_bank_status{(*this).bank_chips_status.clone()};
    }
  };

  struct state_status {
    List<ram_bank_status> ram_sys_status;
    uint64_t cur_bank_status;
    uint64_t sel_chip_status;
    uint64_t sel_reg_status;

    // ACCESSORS
    state_status clone() const {
      return state_status{(*this).ram_sys_status.clone(),
                          (*this).cur_bank_status, (*this).sel_chip_status,
                          (*this).sel_reg_status};
    }
  };

  template <typename T1>
  static List<T1> update_nth_status(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_status<T1>(n_, x, *a10));
      }
    }
  }

  static ram_bank_status get_bank_status(const state_status &s, uint64_t b);
  static ram_chip_status get_chip_status(const ram_bank_status &bk, uint64_t c);
  static ram_reg_status get_reg_status(const ram_chip_status &ch, uint64_t r);
  static ram_reg_status upd_status_in_reg(const ram_reg_status &rg, uint64_t i,
                                          uint64_t v);
  static ram_chip_status upd_reg_in_chip_status(const ram_chip_status &ch,
                                                uint64_t r,
                                                const ram_reg_status &rg);
  static ram_bank_status upd_chip_in_bank_status(const ram_bank_status &bk,
                                                 uint64_t c,
                                                 const ram_chip_status &ch);
  static List<ram_bank_status>
  upd_bank_in_sys_status(const state_status &s, uint64_t b,
                         const ram_bank_status &bk);
  static List<ram_bank_status> ram_write_status_sys(const state_status &s,
                                                    uint64_t idx, uint64_t v);
  static inline const uint64_t test_status_write_chain = []() {
    ram_reg_status rg0 = ram_reg_status{List<uint64_t>::cons(
        UINT64_C(0),
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(0),
                List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()))))};
    ram_chip_status ch0 = ram_chip_status{
        List<ram_reg_status>::cons(rg0, List<ram_reg_status>::nil())};
    ram_bank_status bk0 = ram_bank_status{
        List<ram_chip_status>::cons(ch0, List<ram_chip_status>::nil())};
    state_status s = state_status{
        List<ram_bank_status>::cons(bk0, List<ram_bank_status>::nil()),
        UINT64_C(0), UINT64_C(0), UINT64_C(0)};
    List<ram_bank_status> sys_ =
        ram_write_status_sys(std::move(s), UINT64_C(2), UINT64_C(25));
    ram_bank_status bk_ = ListDef::template nth<ram_bank_status>(
        UINT64_C(0), std::move(sys_),
        ram_bank_status{List<ram_chip_status>::nil()});
    ram_chip_status ch_ = ListDef::template nth<ram_chip_status>(
        UINT64_C(0), std::move(bk_).bank_chips_status,
        ram_chip_status{List<ram_reg_status>::nil()});
    ram_reg_status rg_ = ListDef::template nth<ram_reg_status>(
        UINT64_C(0), std::move(ch_).chip_regs_status,
        ram_reg_status{List<uint64_t>::nil()});
    return ListDef::template nth<uint64_t>(
        UINT64_C(2), std::move(rg_).reg_status, UINT64_C(0));
  }();

  struct ram_reg_sel {
    List<uint64_t> reg_main_sel;
    List<uint64_t> reg_status_sel;

    // ACCESSORS
    ram_reg_sel clone() const {
      return ram_reg_sel{(*this).reg_main_sel.clone(),
                         (*this).reg_status_sel.clone()};
    }
  };

  struct ram_chip_sel {
    List<ram_reg_sel> chip_regs_sel;
    uint64_t chip_port_sel;

    // ACCESSORS
    ram_chip_sel clone() const {
      return ram_chip_sel{(*this).chip_regs_sel.clone(), (*this).chip_port_sel};
    }
  };

  struct ram_bank_sel {
    List<ram_chip_sel> bank_chips_sel;

    // ACCESSORS
    ram_bank_sel clone() const {
      return ram_bank_sel{(*this).bank_chips_sel.clone()};
    }
  };

  struct ram_sel {
    uint64_t sel_chip;
    uint64_t sel_reg;
    uint64_t sel_char;

    // ACCESSORS
    ram_sel clone() const {
      return ram_sel{(*this).sel_chip, (*this).sel_reg, (*this).sel_char};
    }
  };

  struct state_sel {
    List<ram_bank_sel> ram_sys_sel;
    uint64_t cur_bank_sel;
    ram_sel sel_ram;

    // ACCESSORS
    state_sel clone() const {
      return state_sel{(*this).ram_sys_sel.clone(), (*this).cur_bank_sel,
                       (*this).sel_ram.clone()};
    }
  };

  static inline const ram_reg_sel empty_reg_sel =
      ram_reg_sel{List<uint64_t>::nil(), List<uint64_t>::nil()};
  static inline const ram_chip_sel empty_chip_sel =
      ram_chip_sel{List<ram_reg_sel>::nil(), UINT64_C(0)};
  static inline const ram_bank_sel empty_bank_sel =
      ram_bank_sel{List<ram_chip_sel>::nil()};
  static ram_bank_sel get_bank_sel(const state_sel &s, uint64_t b);
  static ram_chip_sel get_chip_sel(const ram_bank_sel &bk, uint64_t c);
  static ram_reg_sel get_regRAM(const ram_chip_sel &ch, uint64_t r);
  static uint64_t get_main_sel(const ram_reg_sel &rg, uint64_t i);
  static uint64_t ram_read_main(const state_sel &s);
  static inline const ram_reg_sel sample_reg_sel = ram_reg_sel{
      List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(
                  UINT64_C(7),
                  List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil())))),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(0),
                  List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()))))};
  static inline const ram_chip_sel sample_chip_sel = ram_chip_sel{
      List<ram_reg_sel>::cons(sample_reg_sel, List<ram_reg_sel>::nil()),
      UINT64_C(3)};
  static inline const ram_bank_sel sample_bank_sel = ram_bank_sel{
      List<ram_chip_sel>::cons(sample_chip_sel, List<ram_chip_sel>::nil())};
  static inline const ram_sel sample_sel =
      ram_sel{UINT64_C(0), UINT64_C(0), UINT64_C(2)};
  static inline const state_sel sample_state_sel = state_sel{
      List<ram_bank_sel>::cons(sample_bank_sel, List<ram_bank_sel>::nil()),
      UINT64_C(0), sample_sel};
  static inline const uint64_t test_read_main_selector =
      ram_read_main(sample_state_sel);

  struct ram_reg_nested {
    List<uint64_t> reg_main_nested;
    List<uint64_t> reg_status_nested;

    // ACCESSORS
    ram_reg_nested clone() const {
      return ram_reg_nested{(*this).reg_main_nested.clone(),
                            (*this).reg_status_nested.clone()};
    }
  };

  struct ram_chip_nested {
    List<ram_reg_nested> chip_regs_nested;
    uint64_t chip_port_nested;

    // ACCESSORS
    ram_chip_nested clone() const {
      return ram_chip_nested{(*this).chip_regs_nested.clone(),
                             (*this).chip_port_nested};
    }
  };

  struct ram_bank_nested {
    List<ram_chip_nested> bank_chips_nested;

    // ACCESSORS
    ram_bank_nested clone() const {
      return ram_bank_nested{(*this).bank_chips_nested.clone()};
    }
  };

  struct ram_sel_nested {
    uint64_t sel_chip_nested;
    uint64_t sel_reg_nested;
    uint64_t sel_char_nested;

    // ACCESSORS
    ram_sel_nested clone() const {
      return ram_sel_nested{(*this).sel_chip_nested, (*this).sel_reg_nested,
                            (*this).sel_char_nested};
    }
  };

  struct state_nested {
    List<ram_bank_nested> ram_sys_nested;
    uint64_t cur_bank_nested;
    ram_sel_nested sel_ram_nested;

    // ACCESSORS
    state_nested clone() const {
      return state_nested{(*this).ram_sys_nested.clone(),
                          (*this).cur_bank_nested,
                          (*this).sel_ram_nested.clone()};
    }
  };

  static inline const ram_reg_nested empty_reg_nested =
      ram_reg_nested{List<uint64_t>::nil(), List<uint64_t>::nil()};
  static inline const ram_chip_nested empty_chip_nested =
      ram_chip_nested{List<ram_reg_nested>::nil(), UINT64_C(0)};
  static inline const ram_bank_nested empty_bank_nested =
      ram_bank_nested{List<ram_chip_nested>::nil()};
  static ram_bank_nested get_bank_nested(const state_nested &s, uint64_t b);
  static ram_chip_nested get_chip_nested(const ram_bank_nested &bk, uint64_t c);
  static ram_reg_nested get_regRAM_nested(const ram_chip_nested &ch,
                                          uint64_t r);
  static uint64_t get_main_nested(const ram_reg_nested &rg, uint64_t i);
  static uint64_t ram_read_main_nested(const state_nested &s);
  static inline const ram_reg_nested sample_reg_nested = ram_reg_nested{
      List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(
                  UINT64_C(7),
                  List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil())))),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(
                  UINT64_C(0),
                  List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()))))};
  static inline const ram_chip_nested sample_chip_nested =
      ram_chip_nested{List<ram_reg_nested>::cons(sample_reg_nested,
                                                 List<ram_reg_nested>::nil()),
                      UINT64_C(3)};
  static inline const ram_bank_nested sample_bank_nested =
      ram_bank_nested{List<ram_chip_nested>::cons(
          sample_chip_nested, List<ram_chip_nested>::nil())};
  static inline const ram_sel_nested sample_sel_nested =
      ram_sel_nested{UINT64_C(0), UINT64_C(0), UINT64_C(2)};
  static inline const state_nested sample_state_nested =
      state_nested{List<ram_bank_nested>::cons(sample_bank_nested,
                                               List<ram_bank_nested>::nil()),
                   UINT64_C(0), sample_sel_nested};
  static inline const uint64_t test_read_nested =
      ram_read_main_nested(sample_state_nested);

  template <typename T1>
  static List<T1> update_nth_frame(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_frame<T1>(n_, x, *a10));
      }
    }
  }

  using reg_frame = List<uint64_t>;
  using chip_frame = List<reg_frame>;
  using bank_frame = List<chip_frame>;
  static reg_frame upd_main_in_reg_frame(const List<uint64_t> &rg, uint64_t i,
                                         uint64_t v);
  static chip_frame upd_reg_in_chip_frame(const List<List<uint64_t>> &ch,
                                          uint64_t r, const List<uint64_t> &rg);
  static bank_frame upd_chip_in_bank_frame(const List<List<List<uint64_t>>> &bk,
                                           uint64_t c,
                                           const List<List<uint64_t>> &ch);
  static inline const bank_frame sample_bank_frame =
      List<List<List<uint64_t>>>::cons(
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(
                      UINT64_C(2), List<uint64_t>::cons(
                                       UINT64_C(3), List<uint64_t>::nil()))),
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil()))),
                  List<List<uint64_t>>::nil())),
          List<List<List<uint64_t>>>::cons(
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(7),
                      List<uint64_t>::cons(
                          UINT64_C(8),
                          List<uint64_t>::cons(UINT64_C(9),
                                               List<uint64_t>::nil()))),
                  List<List<uint64_t>>::cons(
                      List<uint64_t>::cons(
                          UINT64_C(10),
                          List<uint64_t>::cons(
                              UINT64_C(11),
                              List<uint64_t>::cons(UINT64_C(12),
                                                   List<uint64_t>::nil()))),
                      List<List<uint64_t>>::nil())),
              List<List<List<uint64_t>>>::nil()));
  static inline const bank_frame updated_bank_frame = []() {
    List<List<uint64_t>> ch = ListDef::template nth<chip_frame>(
        UINT64_C(0), sample_bank_frame, List<List<uint64_t>>::nil());
    List<uint64_t> rg = ListDef::template nth<reg_frame>(UINT64_C(1), ch,
                                                         List<uint64_t>::nil());
    List<uint64_t> rg_ =
        upd_main_in_reg_frame(std::move(rg), UINT64_C(2), UINT64_C(99));
    List<List<uint64_t>> ch_ =
        upd_reg_in_chip_frame(std::move(ch), UINT64_C(1), std::move(rg_));
    return upd_chip_in_bank_frame(sample_bank_frame, UINT64_C(0),
                                  std::move(ch_));
  }();
  static inline const bool test_write_frame_different_chip =
      ListDef::template nth<uint64_t>(
          UINT64_C(2),
          ListDef::template nth<reg_frame>(
              UINT64_C(0),
              ListDef::template nth<chip_frame>(UINT64_C(1), updated_bank_frame,
                                                List<List<uint64_t>>::nil()),
              List<uint64_t>::nil()),
          UINT64_C(0)) == UINT64_C(7);

  template <typename T1>
  static List<T1> update_nth_preserve(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_preserve<T1>(n_, x, *a10));
      }
    }
  }

  struct state_preserve {
    List<uint64_t> ram_sys_preserve;
    uint64_t cur_bank_preserve;

    // ACCESSORS
    state_preserve clone() const {
      return state_preserve{(*this).ram_sys_preserve.clone(),
                            (*this).cur_bank_preserve};
    }
  };

  static List<uint64_t> ram_write_main_sys_preserve(const state_preserve &s,
                                                    uint64_t v);
  static state_preserve execute_write(const state_preserve &s, uint64_t v);
  static inline const state_preserve sample_preserve = state_preserve{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(
                  UINT64_C(30),
                  List<uint64_t>::cons(UINT64_C(40), List<uint64_t>::nil())))),
      UINT64_C(1)};
  static inline const bool test_write_main_preserves_other_bank =
      ListDef::template nth<uint64_t>(
          UINT64_C(3),
          execute_write(sample_preserve, UINT64_C(99)).ram_sys_preserve,
          UINT64_C(0)) == UINT64_C(40);
  static bool ram_addr_disjointb(uint64_t b1, uint64_t c1, uint64_t r1,
                                 uint64_t i1, uint64_t b2, uint64_t c2,
                                 uint64_t r2, uint64_t i2);
  static inline const uint64_t test_addr_disjoint_bool =
      ((ram_addr_disjointb(UINT64_C(0), UINT64_C(1), UINT64_C(2), UINT64_C(3),
                           UINT64_C(0), UINT64_C(1), UINT64_C(2), UINT64_C(3))
            ? UINT64_C(1)
            : UINT64_C(0)) +
       (ram_addr_disjointb(UINT64_C(0), UINT64_C(1), UINT64_C(2), UINT64_C(3),
                           UINT64_C(0), UINT64_C(1), UINT64_C(2), UINT64_C(4))
            ? UINT64_C(1)
            : UINT64_C(0)));

  struct reg_nested_bank {
    List<uint64_t> status_;

    // ACCESSORS
    reg_nested_bank clone() const {
      return reg_nested_bank{(*this).status_.clone()};
    }
  };

  struct chip_nested_bank {
    List<reg_nested_bank> regs_;

    // ACCESSORS
    chip_nested_bank clone() const {
      return chip_nested_bank{(*this).regs_.clone()};
    }
  };

  struct bank_nested_bank {
    List<chip_nested_bank> chips_;

    // ACCESSORS
    bank_nested_bank clone() const {
      return bank_nested_bank{(*this).chips_.clone()};
    }
  };

  struct state_nested_bank {
    List<bank_nested_bank> banks_;

    // ACCESSORS
    state_nested_bank clone() const {
      return state_nested_bank{(*this).banks_.clone()};
    }
  };

  template <typename T1>
  static List<T1> update_nth_nested_bank(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth_nested_bank<T1>(n_, x, *a10));
      }
    }
  }

  static bank_nested_bank get_bank0(const state_nested_bank &s);
  static chip_nested_bank get_chip0(const bank_nested_bank &b);
  static reg_nested_bank get_reg0(const chip_nested_bank &c);
  static state_nested_bank write_status0(const state_nested_bank &s,
                                         uint64_t v);
  static uint64_t read_status0(const state_nested_bank &s);
  static inline const state_nested_bank sample_nested_bank =
      state_nested_bank{List<bank_nested_bank>::cons(
          bank_nested_bank{List<chip_nested_bank>::cons(
              chip_nested_bank{List<reg_nested_bank>::cons(
                  reg_nested_bank{List<uint64_t>::cons(
                      UINT64_C(3), List<uint64_t>::cons(
                                       UINT64_C(4), List<uint64_t>::nil()))},
                  List<reg_nested_bank>::nil())},
              List<chip_nested_bank>::nil())},
          List<bank_nested_bank>::nil())};
  static inline const uint64_t test_nested_bank_status_write =
      read_status0(write_status0(sample_nested_bank, UINT64_C(7)));
  enum class Item { S_, S_0 };

  template <typename T1> static T1 item_rect(T1 f, T1 f0, Item i) {
    switch (i) {
    case Item::S_: {
      return f;
    }
    case Item::S_0: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 item_rec(T1 f, T1 f0, Item i) {
    switch (i) {
    case Item::S_: {
      return f;
    }
    case Item::S_0: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t score(Item x);
  static inline const uint64_t test_accessor_namespace =
      (score(Item::S_) + score(Item::S_0));
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<std::pair<std::pair<std::pair<std::pair<uint64_t,
                                                                    uint64_t>,
                                                          uint64_t>,
                                                uint64_t>,
                                      uint64_t>,
                            uint64_t>,
                  bool>,
              bool>,
          uint64_t>,
      uint64_t>
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
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_RAM_OPS
