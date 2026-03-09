#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct RamEmptyWf {
  struct ram_reg {
    std::shared_ptr<List<unsigned int>> reg_main;
    std::shared_ptr<List<unsigned int>> reg_status;
  };

  struct ram_chip {
    std::shared_ptr<List<std::shared_ptr<ram_reg>>> chip_regs;
    unsigned int chip_port;
  };

  struct ram_bank {
    std::shared_ptr<List<std::shared_ptr<ram_chip>>> bank_chips;
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;
  };

  static inline const std::shared_ptr<ram_reg> empty_reg =
      std::make_shared<ram_reg>(ram_reg{ListDef::repeat<unsigned int>(0u, 16u),
                                        ListDef::repeat<unsigned int>(0u, 4u)});

  static inline const std::shared_ptr<ram_chip> empty_chip =
      std::make_shared<ram_chip>(ram_chip{
          ListDef::repeat<std::shared_ptr<ram_reg>>(empty_reg, 4u), 0u});

  static inline const std::shared_ptr<ram_bank> empty_bank =
      std::make_shared<ram_bank>(
          ram_bank{ListDef::repeat<std::shared_ptr<ram_chip>>(empty_chip, 4u)});

  static inline const std::shared_ptr<List<std::shared_ptr<ram_bank>>>
      empty_ram = ListDef::repeat<std::shared_ptr<ram_bank>>(empty_bank, 4u);

  static inline const std::shared_ptr<ram_sel> default_sel =
      std::make_shared<ram_sel>(ram_sel{0u, 0u, 0u, 0u});

  static inline const unsigned int default_bank_idx = default_sel->sel_bank;
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List<T1>::ctor::nil_();
  } else {
    unsigned int k = n - 1;
    return List<T1>::ctor::cons_(x, ListDef::repeat<T1>(x, k));
  }
}
