#ifndef INCLUDED_ENCODE_OPS
#define INCLUDED_ENCODE_OPS

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

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct EncodeOps {
  struct instruction1 {
    // TYPES
    struct CLB {};

    struct CMC {};

    struct DAA {};

    struct FIM {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    struct JUN {
      unsigned int d_a0;
    };

    struct LDM1 {
      unsigned int d_a0;
    };

    struct NOP1 {};

    struct RDM {};

    struct TCS {};

    struct WPM {};

    struct WR0 {};

    using variant_t =
        std::variant<CLB, CMC, DAA, FIM, JUN, LDM1, NOP1, RDM, TCS, WPM, WR0>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction1(CLB _v) : d_v_(std::move(_v)) {}

    explicit instruction1(CMC _v) : d_v_(std::move(_v)) {}

    explicit instruction1(DAA _v) : d_v_(std::move(_v)) {}

    explicit instruction1(FIM _v) : d_v_(std::move(_v)) {}

    explicit instruction1(JUN _v) : d_v_(std::move(_v)) {}

    explicit instruction1(LDM1 _v) : d_v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : d_v_(std::move(_v)) {}

    explicit instruction1(RDM _v) : d_v_(std::move(_v)) {}

    explicit instruction1(TCS _v) : d_v_(std::move(_v)) {}

    explicit instruction1(WPM _v) : d_v_(std::move(_v)) {}

    explicit instruction1(WR0 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction1> CLB_() {
        return std::shared_ptr<instruction1>(new instruction1(CLB{}));
      }

      static std::shared_ptr<instruction1> CMC_() {
        return std::shared_ptr<instruction1>(new instruction1(CMC{}));
      }

      static std::shared_ptr<instruction1> DAA_() {
        return std::shared_ptr<instruction1>(new instruction1(DAA{}));
      }

      static std::shared_ptr<instruction1> FIM_(unsigned int a0,
                                                unsigned int a1) {
        return std::shared_ptr<instruction1>(new instruction1(FIM{a0, a1}));
      }

      static std::shared_ptr<instruction1> JUN_(unsigned int a0) {
        return std::shared_ptr<instruction1>(new instruction1(JUN{a0}));
      }

      static std::shared_ptr<instruction1> LDM1_(unsigned int a0) {
        return std::shared_ptr<instruction1>(new instruction1(LDM1{a0}));
      }

      static std::shared_ptr<instruction1> NOP1_() {
        return std::shared_ptr<instruction1>(new instruction1(NOP1{}));
      }

      static std::shared_ptr<instruction1> RDM_() {
        return std::shared_ptr<instruction1>(new instruction1(RDM{}));
      }

      static std::shared_ptr<instruction1> TCS_() {
        return std::shared_ptr<instruction1>(new instruction1(TCS{}));
      }

      static std::shared_ptr<instruction1> WPM_() {
        return std::shared_ptr<instruction1>(new instruction1(WPM{}));
      }

      static std::shared_ptr<instruction1> WR0_() {
        return std::shared_ptr<instruction1>(new instruction1(WR0{}));
      }

      static std::unique_ptr<instruction1> CLB_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(CLB{}));
      }

      static std::unique_ptr<instruction1> CMC_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(CMC{}));
      }

      static std::unique_ptr<instruction1> DAA_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(DAA{}));
      }

      static std::unique_ptr<instruction1> FIM_uptr(unsigned int a0,
                                                    unsigned int a1) {
        return std::unique_ptr<instruction1>(new instruction1(FIM{a0, a1}));
      }

      static std::unique_ptr<instruction1> JUN_uptr(unsigned int a0) {
        return std::unique_ptr<instruction1>(new instruction1(JUN{a0}));
      }

      static std::unique_ptr<instruction1> LDM1_uptr(unsigned int a0) {
        return std::unique_ptr<instruction1>(new instruction1(LDM1{a0}));
      }

      static std::unique_ptr<instruction1> NOP1_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(NOP1{}));
      }

      static std::unique_ptr<instruction1> RDM_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(RDM{}));
      }

      static std::unique_ptr<instruction1> TCS_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(TCS{}));
      }

      static std::unique_ptr<instruction1> WPM_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(WPM{}));
      }

      static std::unique_ptr<instruction1> WR0_uptr() {
        return std::unique_ptr<instruction1>(new instruction1(WR0{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction1_rect(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                              F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                              const T1 f7, const T1 f8, const T1 f9,
                              const std::shared_ptr<instruction1> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction1::CLB _args) -> T1 { return f; },
            [&](const typename instruction1::CMC _args) -> T1 { return f0; },
            [&](const typename instruction1::DAA _args) -> T1 { return f1; },
            [&](const typename instruction1::FIM _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f2(std::move(n), std::move(n0));
            },
            [&](const typename instruction1::JUN _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f3(std::move(n));
            },
            [&](const typename instruction1::LDM1 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f4(std::move(n));
            },
            [&](const typename instruction1::NOP1 _args) -> T1 { return f5; },
            [&](const typename instruction1::RDM _args) -> T1 { return f6; },
            [&](const typename instruction1::TCS _args) -> T1 { return f7; },
            [&](const typename instruction1::WPM _args) -> T1 { return f8; },
            [&](const typename instruction1::WR0 _args) -> T1 { return f9; }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction1_rec(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                             F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                             const T1 f7, const T1 f8, const T1 f9,
                             const std::shared_ptr<instruction1> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction1::CLB _args) -> T1 { return f; },
            [&](const typename instruction1::CMC _args) -> T1 { return f0; },
            [&](const typename instruction1::DAA _args) -> T1 { return f1; },
            [&](const typename instruction1::FIM _args) -> T1 {
              unsigned int n = _args.d_a0;
              unsigned int n0 = _args.d_a1;
              return f2(std::move(n), std::move(n0));
            },
            [&](const typename instruction1::JUN _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f3(std::move(n));
            },
            [&](const typename instruction1::LDM1 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f4(std::move(n));
            },
            [&](const typename instruction1::NOP1 _args) -> T1 { return f5; },
            [&](const typename instruction1::RDM _args) -> T1 { return f6; },
            [&](const typename instruction1::TCS _args) -> T1 { return f7; },
            [&](const typename instruction1::WPM _args) -> T1 { return f8; },
            [&](const typename instruction1::WR0 _args) -> T1 { return f9; }},
        i->v());
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  encode1(const std::shared_ptr<instruction1> &i);
  __attribute__((pure)) static bool
  pair_in_range(const std::pair<unsigned int, unsigned int> p);
  static inline const bool test_encode_bytes_in_range =
      ((((((((((pair_in_range(encode1(instruction1::ctor::CLB_())) &&
                pair_in_range(encode1(instruction1::ctor::CMC_()))) &&
               pair_in_range(encode1(instruction1::ctor::DAA_()))) &&
              pair_in_range(encode1(instruction1::ctor::FIM_(14u, 255u)))) &&
             pair_in_range(encode1(instruction1::ctor::JUN_(4095u)))) &&
            pair_in_range(encode1(instruction1::ctor::LDM1_(15u)))) &&
           pair_in_range(encode1(instruction1::ctor::NOP1_()))) &&
          pair_in_range(encode1(instruction1::ctor::RDM_()))) &&
         pair_in_range(encode1(instruction1::ctor::TCS_()))) &&
        pair_in_range(encode1(instruction1::ctor::WPM_()))) &&
       pair_in_range(encode1(instruction1::ctor::WR0_())));

  struct instruction2 {
    // TYPES
    struct NOP2 {};

    struct LDM2 {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP2, LDM2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction2(NOP2 _v) : d_v_(std::move(_v)) {}

    explicit instruction2(LDM2 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction2> NOP2_() {
        return std::shared_ptr<instruction2>(new instruction2(NOP2{}));
      }

      static std::shared_ptr<instruction2> LDM2_(unsigned int a0) {
        return std::shared_ptr<instruction2>(new instruction2(LDM2{a0}));
      }

      static std::unique_ptr<instruction2> NOP2_uptr() {
        return std::unique_ptr<instruction2>(new instruction2(NOP2{}));
      }

      static std::unique_ptr<instruction2> LDM2_uptr(unsigned int a0) {
        return std::unique_ptr<instruction2>(new instruction2(LDM2{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction2_rect(const T1 f, F1 &&f0,
                              const std::shared_ptr<instruction2> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction2::NOP2 _args) -> T1 { return f; },
            [&](const typename instruction2::LDM2 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction2_rec(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction2> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction2::NOP2 _args) -> T1 { return f; },
            [&](const typename instruction2::LDM2 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  encode2(const std::shared_ptr<instruction2> &i);
  static std::shared_ptr<List<unsigned int>> encode_list2(
      const std::shared_ptr<List<std::shared_ptr<instruction2>>> &prog);
  static inline const unsigned int test_encode_list_byte_count =
      encode_list2(
          List<std::shared_ptr<instruction2>>::ctor::Cons_(
              instruction2::ctor::NOP2_(),
              List<std::shared_ptr<instruction2>>::ctor::Cons_(
                  instruction2::ctor::LDM2_(5u),
                  List<std::shared_ptr<instruction2>>::ctor::Cons_(
                      instruction2::ctor::NOP2_(),
                      List<std::shared_ptr<instruction2>>::ctor::Nil_()))))
          ->length();

  struct instruction3 {
    // TYPES
    struct NOP3 {};

    struct LDM3 {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP3, LDM3>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit instruction3(NOP3 _v) : d_v_(std::move(_v)) {}

    explicit instruction3(LDM3 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<instruction3> NOP3_() {
        return std::shared_ptr<instruction3>(new instruction3(NOP3{}));
      }

      static std::shared_ptr<instruction3> LDM3_(unsigned int a0) {
        return std::shared_ptr<instruction3>(new instruction3(LDM3{a0}));
      }

      static std::unique_ptr<instruction3> NOP3_uptr() {
        return std::unique_ptr<instruction3>(new instruction3(NOP3{}));
      }

      static std::unique_ptr<instruction3> LDM3_uptr(unsigned int a0) {
        return std::unique_ptr<instruction3>(new instruction3(LDM3{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction3_rect(const T1 f, F1 &&f0,
                              const std::shared_ptr<instruction3> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction3::NOP3 _args) -> T1 { return f; },
            [&](const typename instruction3::LDM3 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction3_rec(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction3> &i) {
    return std::visit(
        Overloaded{
            [&](const typename instruction3::NOP3 _args) -> T1 { return f; },
            [&](const typename instruction3::LDM3 _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f0(std::move(n));
            }},
        i->v());
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  encode3(const std::shared_ptr<instruction3> &i);
  static std::shared_ptr<List<unsigned int>> encode_list3(
      const std::shared_ptr<List<std::shared_ptr<instruction3>>> &prog);
  static inline const unsigned int test_instruction_byte_stream_encode =
      encode_list3(
          List<std::shared_ptr<instruction3>>::ctor::Cons_(
              instruction3::ctor::NOP3_(),
              List<std::shared_ptr<instruction3>>::ctor::Cons_(
                  instruction3::ctor::LDM3_(3u),
                  List<std::shared_ptr<instruction3>>::ctor::Cons_(
                      instruction3::ctor::LDM3_(12u),
                      List<std::shared_ptr<instruction3>>::ctor::Nil_()))))
          ->length();
  static inline const std::pair<std::pair<bool, unsigned int>, unsigned int> t =
      std::make_pair(std::make_pair(test_encode_bytes_in_range,
                                    test_encode_list_byte_count),
                     test_instruction_byte_stream_encode);
};

#endif // INCLUDED_ENCODE_OPS
