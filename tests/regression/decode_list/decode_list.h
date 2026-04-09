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
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
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
    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

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
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::LDM _args) -> T1 {
              return f0(_args.d_a0);
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0,
                            const std::shared_ptr<instruction> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction::NOP _args) -> T1 { return f; },
            [&](const typename instruction::LDM _args) -> T1 {
              return f0(_args.d_a0);
            }},
        i->v());
  }

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);
  static std::shared_ptr<List<std::shared_ptr<instruction>>>
  decode_list(const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const unsigned int t_empty =
      decode_list(List<unsigned int>::nil())->length();
  static inline const unsigned int t_odd_tail = []() {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<instruction>>::Nil _args0)
                -> unsigned int { return 0u; },
            [](const typename List<std::shared_ptr<instruction>>::Cons _args0)
                -> unsigned int {
              return std::visit(
                  Overloaded{
                      [&](const typename instruction::NOP _args1)
                          -> unsigned int {
                        return std::visit(
                            Overloaded{
                                [](const typename List<
                                    std::shared_ptr<instruction>>::Nil _args2)
                                    -> unsigned int { return 1u; },
                                [](const typename List<
                                    std::shared_ptr<instruction>>::Cons _args2)
                                    -> unsigned int { return 0u; }},
                            _args0.d_a1->v());
                      },
                      [](const typename instruction::LDM _args1)
                          -> unsigned int { return 0u; }},
                  _args0.d_a0->v());
            }},
        decode_list(List<unsigned int>::cons(
                        0u, List<unsigned int>::cons(
                                99u, List<unsigned int>::cons(
                                         42u, List<unsigned int>::nil()))))
            ->v());
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
