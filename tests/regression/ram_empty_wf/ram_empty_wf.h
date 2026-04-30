#ifndef INCLUDED_RAM_EMPTY_WF
#define INCLUDED_RAM_EMPTY_WF

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
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
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
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct ListDef {
  template <typename T1>
  static List<T1> repeat(const T1 x, const unsigned int &n);
};

struct RamEmptyWf {
  struct ram_reg {
    List<unsigned int> reg_main;
    List<unsigned int> reg_status;

    // ACCESSORS
    ram_reg clone() const {
      return ram_reg{(*(this)).reg_main.clone(), (*(this)).reg_status.clone()};
    }
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    unsigned int chip_port;

    // ACCESSORS
    ram_chip clone() const {
      return ram_chip{(*(this)).chip_regs.clone(), (*(this)).chip_port};
    }
  };

  struct ram_bank {
    List<ram_chip> bank_chips;

    // ACCESSORS
    ram_bank clone() const { return ram_bank{(*(this)).bank_chips.clone()}; }
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;

    // ACCESSORS
    ram_sel clone() const {
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
List<T1> ListDef::repeat(const T1 x, const unsigned int &n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_EMPTY_WF
