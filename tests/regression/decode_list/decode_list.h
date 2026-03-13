#ifndef INCLUDED_DECODE_LIST
#define INCLUDED_DECODE_LIST

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

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
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
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

    // CREATORS
    explicit instruction(NOP _v) : d_v_(std::move(_v)) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction> NOP_() {
        return std::shared_ptr<instruction>(new instruction(NOP{}));
      }

      static std::shared_ptr<instruction> LDM_(unsigned int a0) {
        return std::shared_ptr<instruction>(new instruction(LDM{a0}));
      }

      static std::unique_ptr<instruction> NOP_uptr() {
        return std::unique_ptr<instruction>(new instruction(NOP{}));
      }

      static std::unique_ptr<instruction> LDM_uptr(unsigned int a0) {
        return std::unique_ptr<instruction>(new instruction(LDM{a0}));
      }
    };

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
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
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
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  static std::shared_ptr<instruction> decode(const unsigned int b1,
                                             const unsigned int b2);
  static std::shared_ptr<List<std::shared_ptr<instruction>>>
  decode_list(const std::shared_ptr<List<unsigned int>> &bytes);
  static inline const unsigned int t_empty =
      decode_list(List<unsigned int>::ctor::Nil_())->length();
  static inline const unsigned int t_odd_tail = []() {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<instruction>>::Nil _args)
                -> unsigned int { return 0u; },
            [](const typename List<std::shared_ptr<instruction>>::Cons _args)
                -> unsigned int {
              std::shared_ptr<instruction> i = _args.d_a0;
              std::shared_ptr<List<std::shared_ptr<instruction>>> l =
                  _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename instruction::NOP _args)
                          -> unsigned int {
                        return std::visit(
                            Overloaded{
                                [](const typename List<
                                    std::shared_ptr<instruction>>::Nil _args)
                                    -> unsigned int { return 1u; },
                                [](const typename List<
                                    std::shared_ptr<instruction>>::Cons _args)
                                    -> unsigned int { return 0u; }},
                            std::move(l)->v());
                      },
                      [](const typename instruction::LDM _args)
                          -> unsigned int { return 0u; }},
                  std::move(i)->v());
            }},
        decode_list(
            List<unsigned int>::ctor::Cons_(
                0u, List<unsigned int>::ctor::Cons_(
                        99u, List<unsigned int>::ctor::Cons_(
                                 42u, List<unsigned int>::ctor::Nil_()))))
            ->v());
  }();
  static inline const unsigned int t_pair_count =
      decode_list(
          List<unsigned int>::ctor::Cons_(
              0u, List<unsigned int>::ctor::Cons_(
                      1u, List<unsigned int>::ctor::Cons_(
                              2u, List<unsigned int>::ctor::Cons_(
                                      3u, List<unsigned int>::ctor::Nil_())))))
          ->length();
  static inline const unsigned int t_single_pair =
      decode_list(List<unsigned int>::ctor::Cons_(
                      0u, List<unsigned int>::ctor::Cons_(
                              7u, List<unsigned int>::ctor::Nil_())))
          ->length();
};

#endif // INCLUDED_DECODE_LIST
