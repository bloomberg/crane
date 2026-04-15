#ifndef INCLUDED_DECODE_LIST
#define INCLUDED_DECODE_LIST

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

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }
};

struct DecodeList {
  struct instruction {
    // TYPES
    struct NOP {};

    struct LDM {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP, LDM>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction> nop() {
      return std::make_shared<instruction>(NOP{});
    }

    static std::shared_ptr<instruction> ldm(unsigned int a0) {
      return std::make_shared<instruction>(LDM{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    if (std::holds_alternative<typename instruction::NOP>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i->v());
      return f0(d_a0);
    }
  }

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);
  static std::shared_ptr<List<std::shared_ptr<instruction>>>
  decode_list(const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const unsigned int t_empty =
      decode_list(List<unsigned int>::nil())->length();
  static inline const unsigned int t_odd_tail = []() {
    auto &&_sv0 = decode_list(List<unsigned int>::cons(
        0u,
        List<unsigned int>::cons(
            99u, List<unsigned int>::cons(42u, List<unsigned int>::nil()))));
    if (std::holds_alternative<
            typename List<std::shared_ptr<instruction>>::Nil>(_sv0->v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<std::shared_ptr<instruction>>::Cons>(
              _sv0->v());
      if (std::holds_alternative<typename instruction::NOP>(d_a00->v())) {
        if (std::holds_alternative<
                typename List<std::shared_ptr<instruction>>::Nil>(d_a10->v())) {
          return 1u;
        } else {
          return 0u;
        }
      } else {
        return 0u;
      }
    }
  }();
  static inline const unsigned int t_pair_count =
      decode_list(List<unsigned int>::cons(
                      0u, List<unsigned int>::cons(
                              1u, List<unsigned int>::cons(
                                      2u, List<unsigned int>::cons(
                                              3u, List<unsigned int>::nil())))))
          ->length();
  static inline const unsigned int t_single_pair =
      decode_list(
          List<unsigned int>::cons(
              0u, List<unsigned int>::cons(7u, List<unsigned int>::nil())))
          ->length();
};

#endif // INCLUDED_DECODE_LIST
