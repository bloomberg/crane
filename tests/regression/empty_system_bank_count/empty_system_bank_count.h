#ifndef INCLUDED_EMPTY_SYSTEM_BANK_COUNT
#define INCLUDED_EMPTY_SYSTEM_BANK_COUNT

#include <memory>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct EmptySystemBankCount {
  struct ram_reg {
    List<uint64_t> reg_main;
    List<uint64_t> reg_status;

    // ACCESSORS
    ram_reg clone() const {
      return ram_reg{(*this).reg_main.clone(), (*this).reg_status.clone()};
    }
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    uint64_t chip_port;

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

  static inline const uint64_t NBANKS = UINT64_C(4);
  static inline const uint64_t NCHIPS = UINT64_C(4);
  static inline const uint64_t NREGS = UINT64_C(4);
  static inline const uint64_t NMAIN = UINT64_C(16);
  static inline const uint64_t NSTAT = UINT64_C(4);
  static inline const ram_reg empty_reg =
      ram_reg{ListDef::template repeat<uint64_t>(UINT64_C(0), NMAIN),
              ListDef::template repeat<uint64_t>(UINT64_C(0), NSTAT)};
  static inline const ram_chip empty_chip = ram_chip{
      ListDef::template repeat<ram_reg>(empty_reg, NREGS), UINT64_C(0)};
  static inline const ram_bank empty_bank =
      ram_bank{ListDef::template repeat<ram_chip>(empty_chip, NCHIPS)};
  static inline const List<ram_bank> empty_sys =
      ListDef::template repeat<ram_bank>(empty_bank, NBANKS);
  static inline const uint64_t t = empty_sys.length();
};

template <typename T1> List<T1> ListDef::repeat(T1 x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_EMPTY_SYSTEM_BANK_COUNT
