#ifndef INCLUDED_RAM_EMPTY_WF
#define INCLUDED_RAM_EMPTY_WF

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(const T1 &x, uint64_t n);
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

template <typename T1> List<T1> ListDef::repeat(const T1 &x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_EMPTY_WF
