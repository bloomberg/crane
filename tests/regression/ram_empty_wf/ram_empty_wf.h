#ifndef INCLUDED_RAM_EMPTY_WF
#define INCLUDED_RAM_EMPTY_WF

#include <any>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct RamEmptyWf {
  struct ram_reg {
    List<uint64_t> reg_main;
    List<uint64_t> reg_status;
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    uint64_t chip_port;
  };

  struct ram_bank {
    List<ram_chip> bank_chips;
  };

  struct ram_sel {
    uint64_t sel_bank;
    uint64_t sel_chip;
    uint64_t sel_reg;
    uint64_t sel_char;
  };

  static inline const ram_reg empty_reg =
      ram_reg{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
              ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(4))};
  static inline const ram_chip empty_chip = ram_chip{
      ListDef::template repeat<ram_reg>(empty_reg, UINT64_C(4)), UINT64_C(0)};
  static inline const ram_bank empty_bank =
      ram_bank{ListDef::template repeat<ram_chip>(empty_chip, UINT64_C(4))};
  static inline const List<ram_bank> empty_ram =
      ListDef::template repeat<ram_bank>(empty_bank, UINT64_C(4));
  static inline const ram_sel default_sel =
      ram_sel{UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(0)};
  static inline const uint64_t default_bank_idx = default_sel.sel_bank;
};

template <typename T1> List<T1> ListDef::repeat(T1 x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_EMPTY_WF
