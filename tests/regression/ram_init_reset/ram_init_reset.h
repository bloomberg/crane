#ifndef INCLUDED_RAM_INIT_RESET
#define INCLUDED_RAM_INIT_RESET

#include <memory>
#include <optional>
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
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, unsigned int n);
};

struct RamInitReset {
  template <typename T1>
  static List<T1> update_nth(unsigned int n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct ram_reg {
    List<unsigned int> reg_main;
    List<unsigned int> reg_status;

    // ACCESSORS
    ram_reg clone() const {
      return ram_reg{(*this).reg_main.clone(), (*this).reg_status.clone()};
    }
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    unsigned int chip_port;

    // ACCESSORS
    ram_chip clone() const {
      return ram_chip{(*this).chip_regs.clone(), (*this).chip_port};
    }
  };

  struct ram_bank {
    List<ram_chip> bank_chips;

    // ACCESSORS
    ram_bank clone() const { return ram_bank{(*this).bank_chips.clone()}; }
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;

    // ACCESSORS
    ram_sel clone() const {
      return ram_sel{(*this).sel_bank, (*this).sel_chip, (*this).sel_reg,
                     (*this).sel_char};
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
    state clone() const {
      return state{(*this).state_regs.clone(),  (*this).state_acc,
                   (*this).state_carry,         (*this).state_pc,
                   (*this).state_stack.clone(), (*this).state_ram.clone(),
                   (*this).state_sel.clone(),   (*this).state_rom.clone()};
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
  static state reset_state(const state &s);
  static std::pair<std::optional<unsigned int>, state> pop_stack(state s);
  static inline const unsigned int reset_pc = reset_state(init_state).state_pc;
};

template <typename T1> List<T1> ListDef::repeat(T1 x, unsigned int n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_INIT_RESET
