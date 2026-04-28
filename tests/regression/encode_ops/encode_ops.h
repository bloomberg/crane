#ifndef INCLUDED_ENCODE_OPS
#define INCLUDED_ENCODE_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
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

  public:
    // CREATORS
    instruction1() {}

    explicit instruction1(CLB _v) : d_v_(_v) {}

    explicit instruction1(CMC _v) : d_v_(_v) {}

    explicit instruction1(DAA _v) : d_v_(_v) {}

    explicit instruction1(FIM _v) : d_v_(std::move(_v)) {}

    explicit instruction1(JUN _v) : d_v_(std::move(_v)) {}

    explicit instruction1(LDM1 _v) : d_v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : d_v_(_v) {}

    explicit instruction1(RDM _v) : d_v_(_v) {}

    explicit instruction1(TCS _v) : d_v_(_v) {}

    explicit instruction1(WPM _v) : d_v_(_v) {}

    explicit instruction1(WR0 _v) : d_v_(_v) {}

    instruction1(const instruction1 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction1(instruction1 &&_other) : d_v_(std::move(_other.d_v_)) {}

    instruction1 &operator=(const instruction1 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instruction1 &operator=(instruction1 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction1 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<CLB>(_sv.v())) {
        return instruction1(CLB{});
      } else if (std::holds_alternative<CMC>(_sv.v())) {
        return instruction1(CMC{});
      } else if (std::holds_alternative<DAA>(_sv.v())) {
        return instruction1(DAA{});
      } else if (std::holds_alternative<FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<FIM>(_sv.v());
        return instruction1(FIM{d_a0, d_a1});
      } else if (std::holds_alternative<JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN>(_sv.v());
        return instruction1(JUN{d_a0});
      } else if (std::holds_alternative<LDM1>(_sv.v())) {
        const auto &[d_a0] = std::get<LDM1>(_sv.v());
        return instruction1(LDM1{d_a0});
      } else if (std::holds_alternative<NOP1>(_sv.v())) {
        return instruction1(NOP1{});
      } else if (std::holds_alternative<RDM>(_sv.v())) {
        return instruction1(RDM{});
      } else if (std::holds_alternative<TCS>(_sv.v())) {
        return instruction1(TCS{});
      } else if (std::holds_alternative<WPM>(_sv.v())) {
        return instruction1(WPM{});
      } else {
        return instruction1(WR0{});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction1 clb() {
      return instruction1(CLB{});
    }

    __attribute__((pure)) static instruction1 cmc() {
      return instruction1(CMC{});
    }

    __attribute__((pure)) static instruction1 daa() {
      return instruction1(DAA{});
    }

    __attribute__((pure)) static instruction1 fim(unsigned int a0,
                                                  unsigned int a1) {
      return instruction1(FIM{std::move(a0), std::move(a1)});
    }

    __attribute__((pure)) static instruction1 jun(unsigned int a0) {
      return instruction1(JUN{std::move(a0)});
    }

    __attribute__((pure)) static instruction1 ldm1(unsigned int a0) {
      return instruction1(LDM1{std::move(a0)});
    }

    __attribute__((pure)) static instruction1 nop1() {
      return instruction1(NOP1{});
    }

    __attribute__((pure)) static instruction1 rdm() {
      return instruction1(RDM{});
    }

    __attribute__((pure)) static instruction1 tcs() {
      return instruction1(TCS{});
    }

    __attribute__((pure)) static instruction1 wpm() {
      return instruction1(WPM{});
    }

    __attribute__((pure)) static instruction1 wr0() {
      return instruction1(WR0{});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode1() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::CLB>(_sv.v())) {
        return std::make_pair(240u, 0u);
      } else if (std::holds_alternative<typename instruction1::CMC>(_sv.v())) {
        return std::make_pair(243u, 0u);
      } else if (std::holds_alternative<typename instruction1::DAA>(_sv.v())) {
        return std::make_pair(251u, 0u);
      } else if (std::holds_alternative<typename instruction1::FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::FIM>(_sv.v());
        return std::make_pair(
            (32u + (((d_a0 - (2u ? d_a0 % 2u : d_a0)) > d_a0
                         ? 0
                         : (d_a0 - (2u ? d_a0 % 2u : d_a0))))),
            (256u ? d_a1 % 256u : d_a1));
      } else if (std::holds_alternative<typename instruction1::JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::JUN>(_sv.v());
        return std::make_pair((64u + (256u ? d_a0 / 256u : 0)),
                              (256u ? d_a0 % 256u : d_a0));
      } else if (std::holds_alternative<typename instruction1::LDM1>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::LDM1>(_sv.v());
        return std::make_pair((208u + (16u ? d_a0 % 16u : d_a0)), 0u);
      } else if (std::holds_alternative<typename instruction1::NOP1>(_sv.v())) {
        return std::make_pair(0u, 0u);
      } else if (std::holds_alternative<typename instruction1::RDM>(_sv.v())) {
        return std::make_pair(233u, 0u);
      } else if (std::holds_alternative<typename instruction1::TCS>(_sv.v())) {
        return std::make_pair(249u, 0u);
      } else if (std::holds_alternative<typename instruction1::WPM>(_sv.v())) {
        return std::make_pair(227u, 0u);
      } else {
        return std::make_pair(228u, 0u);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
              MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
    T1 instruction1_rec(const T1 f, const T1 f0, const T1 f1, F3 &&f2, F4 &&f3,
                        F5 &&f4, const T1 f5, const T1 f6, const T1 f7,
                        const T1 f8, const T1 f9) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::CLB>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instruction1::CMC>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename instruction1::DAA>(_sv.v())) {
        return f1;
      } else if (std::holds_alternative<typename instruction1::FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::FIM>(_sv.v());
        return f2(d_a0, d_a1);
      } else if (std::holds_alternative<typename instruction1::JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::JUN>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instruction1::LDM1>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::LDM1>(_sv.v());
        return f4(d_a0);
      } else if (std::holds_alternative<typename instruction1::NOP1>(_sv.v())) {
        return f5;
      } else if (std::holds_alternative<typename instruction1::RDM>(_sv.v())) {
        return f6;
      } else if (std::holds_alternative<typename instruction1::TCS>(_sv.v())) {
        return f7;
      } else if (std::holds_alternative<typename instruction1::WPM>(_sv.v())) {
        return f8;
      } else {
        return f9;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
              MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
    T1 instruction1_rect(const T1 f, const T1 f0, const T1 f1, F3 &&f2, F4 &&f3,
                         F5 &&f4, const T1 f5, const T1 f6, const T1 f7,
                         const T1 f8, const T1 f9) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction1::CLB>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename instruction1::CMC>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename instruction1::DAA>(_sv.v())) {
        return f1;
      } else if (std::holds_alternative<typename instruction1::FIM>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::FIM>(_sv.v());
        return f2(d_a0, d_a1);
      } else if (std::holds_alternative<typename instruction1::JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::JUN>(_sv.v());
        return f3(d_a0);
      } else if (std::holds_alternative<typename instruction1::LDM1>(_sv.v())) {
        const auto &[d_a0] = std::get<typename instruction1::LDM1>(_sv.v());
        return f4(d_a0);
      } else if (std::holds_alternative<typename instruction1::NOP1>(_sv.v())) {
        return f5;
      } else if (std::holds_alternative<typename instruction1::RDM>(_sv.v())) {
        return f6;
      } else if (std::holds_alternative<typename instruction1::TCS>(_sv.v())) {
        return f7;
      } else if (std::holds_alternative<typename instruction1::WPM>(_sv.v())) {
        return f8;
      } else {
        return f9;
      }
    }
  };

  __attribute__((pure)) static bool
  pair_in_range(const std::pair<unsigned int, unsigned int> &p);
  static inline const bool test_encode_bytes_in_range =
      ((((((((((pair_in_range(instruction1::clb().encode1()) &&
                pair_in_range(instruction1::cmc().encode1())) &&
               pair_in_range(instruction1::daa().encode1())) &&
              pair_in_range(instruction1::fim(14u, 255u).encode1())) &&
             pair_in_range(instruction1::jun(4095u).encode1())) &&
            pair_in_range(instruction1::ldm1(15u).encode1())) &&
           pair_in_range(instruction1::nop1().encode1())) &&
          pair_in_range(instruction1::rdm().encode1())) &&
         pair_in_range(instruction1::tcs().encode1())) &&
        pair_in_range(instruction1::wpm().encode1())) &&
       pair_in_range(instruction1::wr0().encode1()));

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

  public:
    // CREATORS
    instruction2() {}

    explicit instruction2(NOP2 _v) : d_v_(_v) {}

    explicit instruction2(LDM2 _v) : d_v_(std::move(_v)) {}

    instruction2(const instruction2 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction2(instruction2 &&_other) : d_v_(std::move(_other.d_v_)) {}

    instruction2 &operator=(const instruction2 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instruction2 &operator=(instruction2 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction2 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP2>(_sv.v())) {
        return instruction2(NOP2{});
      } else {
        const auto &[d_a0] = std::get<LDM2>(_sv.v());
        return instruction2(LDM2{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction2 nop2() {
      return instruction2(NOP2{});
    }

    __attribute__((pure)) static instruction2 ldm2(unsigned int a0) {
      return instruction2(LDM2{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode2() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction2::NOP2>(_sv.v())) {
        return std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0] = std::get<typename instruction2::LDM2>(_sv.v());
        return std::make_pair(13u, (16u ? d_a0 % 16u : d_a0));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 instruction2_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction2::NOP2>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename instruction2::LDM2>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 instruction2_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction2::NOP2>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename instruction2::LDM2>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  __attribute__((pure)) static List<unsigned int>
  encode_list2(const List<instruction2> &prog);
  static inline const unsigned int test_encode_list_byte_count =
      encode_list2(
          List<instruction2>::cons(
              instruction2::nop2(),
              List<instruction2>::cons(
                  instruction2::ldm2(5u),
                  List<instruction2>::cons(instruction2::nop2(),
                                           List<instruction2>::nil()))))
          .length();

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

  public:
    // CREATORS
    instruction3() {}

    explicit instruction3(NOP3 _v) : d_v_(_v) {}

    explicit instruction3(LDM3 _v) : d_v_(std::move(_v)) {}

    instruction3(const instruction3 &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction3(instruction3 &&_other) : d_v_(std::move(_other.d_v_)) {}

    instruction3 &operator=(const instruction3 &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instruction3 &operator=(instruction3 &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction3 clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP3>(_sv.v())) {
        return instruction3(NOP3{});
      } else {
        const auto &[d_a0] = std::get<LDM3>(_sv.v());
        return instruction3(LDM3{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static instruction3 nop3() {
      return instruction3(NOP3{});
    }

    __attribute__((pure)) static instruction3 ldm3(unsigned int a0) {
      return instruction3(LDM3{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode3() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction3::NOP3>(_sv.v())) {
        return std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0] = std::get<typename instruction3::LDM3>(_sv.v());
        return std::make_pair(((13u * 16u) + (16u ? d_a0 % 16u : d_a0)), 0u);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 instruction3_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction3::NOP3>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename instruction3::LDM3>(_sv.v());
        return f0(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F1>
    T1 instruction3_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename instruction3::NOP3>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0] = std::get<typename instruction3::LDM3>(_sv.v());
        return f0(d_a0);
      }
    }
  };

  __attribute__((pure)) static List<unsigned int>
  encode_list3(const List<instruction3> &prog);
  static inline const unsigned int test_instruction_byte_stream_encode =
      encode_list3(
          List<instruction3>::cons(
              instruction3::nop3(),
              List<instruction3>::cons(
                  instruction3::ldm3(3u),
                  List<instruction3>::cons(instruction3::ldm3(12u),
                                           List<instruction3>::nil()))))
          .length();
  static inline const std::pair<std::pair<bool, unsigned int>, unsigned int> t =
      std::make_pair(std::make_pair(test_encode_bytes_in_range,
                                    test_encode_list_byte_count),
                     test_instruction_byte_stream_encode);
};

#endif // INCLUDED_ENCODE_OPS
