#ifndef INCLUDED_BANK_LOOKUP_DEFAULT
#define INCLUDED_BANK_LOOKUP_DEFAULT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
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

template <typename T1>
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_BANK_LOOKUP_DEFAULT
