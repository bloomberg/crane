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
  unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
};

struct PromParamsLargeState {
  struct state {
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> regs;
    bool carry;
    unsigned int pc;
    std::shared_ptr<List<unsigned int>> stack;
    std::shared_ptr<List<unsigned int>> ram_sys;
    unsigned int cur_bank;
    unsigned int sel_ram;
    std::shared_ptr<List<unsigned int>> rom_ports;
    unsigned int sel_rom;
    std::shared_ptr<List<unsigned int>> rom;
    bool test_pin;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  static unsigned int acc(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  regs(const std::shared_ptr<state> &s);

  static bool carry(const std::shared_ptr<state> &s);

  static unsigned int pc(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  stack(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  ram_sys(const std::shared_ptr<state> &s);

  static unsigned int cur_bank(const std::shared_ptr<state> &s);

  static unsigned int sel_ram(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  rom_ports(const std::shared_ptr<state> &s);

  static unsigned int sel_rom(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  rom(const std::shared_ptr<state> &s);

  static bool test_pin(const std::shared_ptr<state> &s);

  static unsigned int prom_addr(const std::shared_ptr<state> &s);

  static unsigned int prom_data(const std::shared_ptr<state> &s);

  static bool prom_enable(const std::shared_ptr<state> &s);

  static std::shared_ptr<state> set_prom_params(std::shared_ptr<state> s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);

  static inline const unsigned int t = []() {
    return [](void) {
      std::unique_ptr<state> s = std::make_unique<state>(state{
          (0 + 1),
          List<unsigned int>::ctor::cons_(
              ((0 + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  (((0 + 1) + 1) + 1), List<unsigned int>::ctor::nil_())),
          false, ((((0 + 1) + 1) + 1) + 1),
          List<unsigned int>::ctor::cons_((((((0 + 1) + 1) + 1) + 1) + 1),
                                          List<unsigned int>::ctor::nil_()),
          List<unsigned int>::ctor::cons_(((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                                          List<unsigned int>::ctor::nil_()),
          0, 0,
          List<unsigned int>::ctor::cons_(
              (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::nil_()),
          0,
          List<unsigned int>::ctor::cons_(
              ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List<unsigned int>::ctor::nil_())),
          true, 0, 0, false});
 std::shared_ptr<state> s_ = set_prom_params(std::move(s), (((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), true);
 return ((s_->prom_addr +
          [&](void) {
            if (s_->prom_enable) {
              return std::move(s_)->prom_data;
            } else {
              return 0;
            }
          }()) +
         s_->regs->length());
    }();
  }();
};
