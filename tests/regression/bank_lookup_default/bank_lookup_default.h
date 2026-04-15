#ifndef INCLUDED_BANK_LOOKUP_DEFAULT
#define INCLUDED_BANK_LOOKUP_DEFAULT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m.d_a0;
      }
    } else {
      unsigned int m = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &_m0 = *std::get_if<typename List<t_A>::Cons>(&this->v());
        return _m0.d_a1->nth(m, default0);
      }
    }
  }

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &_m = *std::get_if<typename List<t_A>::Cons>(&this->v());
      return (_m.d_a1->length() + 1);
    }
  }
};

struct BankLookupDefault {
  struct ram_chip {
    unsigned int chip_port;
  };

  struct ram_bank {
    std::shared_ptr<List<std::shared_ptr<ram_chip>>> bank_chips;
  };

  struct state {
    std::shared_ptr<List<std::shared_ptr<ram_bank>>> ram_sys;
  };

  static inline const std::shared_ptr<ram_chip> empty_chip =
      std::make_shared<ram_chip>(ram_chip{0u});
  static inline const std::shared_ptr<ram_bank> empty_bank =
      std::make_shared<ram_bank>(
          ram_bank{List<std::shared_ptr<ram_chip>>::nil()});
  static std::shared_ptr<ram_bank> get_bank(const std::shared_ptr<state> &s,
                                            const unsigned int b);
  static inline const std::shared_ptr<state> sample_state =
      std::make_shared<state>(state{List<std::shared_ptr<ram_bank>>::cons(
          std::make_shared<ram_bank>(
              ram_bank{List<std::shared_ptr<ram_chip>>::cons(
                  empty_chip, List<std::shared_ptr<ram_chip>>::nil())}),
          List<std::shared_ptr<ram_bank>>::nil())});
  static inline const unsigned int t =
      get_bank(sample_state, 7u)->bank_chips->length();
};

#endif // INCLUDED_BANK_LOOKUP_DEFAULT
