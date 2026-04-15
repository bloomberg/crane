#ifndef INCLUDED_ENCODE_OPS
#define INCLUDED_ENCODE_OPS

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

    static std::shared_ptr<instruction1> clb() {
      return std::make_shared<instruction1>(CLB{});
    }

    static std::shared_ptr<instruction1> cmc() {
      return std::make_shared<instruction1>(CMC{});
    }

    static std::shared_ptr<instruction1> daa() {
      return std::make_shared<instruction1>(DAA{});
    }

    static std::shared_ptr<instruction1> fim(unsigned int a0, unsigned int a1) {
      return std::make_shared<instruction1>(FIM{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<instruction1> jun(unsigned int a0) {
      return std::make_shared<instruction1>(JUN{std::move(a0)});
    }

    static std::shared_ptr<instruction1> ldm1(unsigned int a0) {
      return std::make_shared<instruction1>(LDM1{std::move(a0)});
    }

    static std::shared_ptr<instruction1> nop1() {
      return std::make_shared<instruction1>(NOP1{});
    }

    static std::shared_ptr<instruction1> rdm() {
      return std::make_shared<instruction1>(RDM{});
    }

    static std::shared_ptr<instruction1> tcs() {
      return std::make_shared<instruction1>(TCS{});
    }

    static std::shared_ptr<instruction1> wpm() {
      return std::make_shared<instruction1>(WPM{});
    }

    static std::shared_ptr<instruction1> wr0() {
      return std::make_shared<instruction1>(WR0{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode1() const {
      if (std::holds_alternative<typename instruction1::CLB>(this->v())) {
        return std::make_pair(240u, 0u);
      } else if (std::holds_alternative<typename instruction1::CMC>(
                     this->v())) {
        return std::make_pair(243u, 0u);
      } else if (std::holds_alternative<typename instruction1::DAA>(
                     this->v())) {
        return std::make_pair(251u, 0u);
      } else if (std::holds_alternative<typename instruction1::FIM>(
                     this->v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename instruction1::FIM>(this->v());
        return std::make_pair(
            (32u + (((d_a0 - (2u ? d_a0 % 2u : d_a0)) > d_a0
                         ? 0
                         : (d_a0 - (2u ? d_a0 % 2u : d_a0))))),
            (256u ? d_a1 % 256u : d_a1));
      } else if (std::holds_alternative<typename instruction1::JUN>(
                     this->v())) {
        const auto &[d_a0] = std::get<typename instruction1::JUN>(this->v());
        return std::make_pair((64u + (256u ? d_a0 / 256u : 0)),
                              (256u ? d_a0 % 256u : d_a0));
      } else if (std::holds_alternative<typename instruction1::LDM1>(
                     this->v())) {
        const auto &[d_a0] = std::get<typename instruction1::LDM1>(this->v());
        return std::make_pair((208u + (16u ? d_a0 % 16u : d_a0)), 0u);
      } else if (std::holds_alternative<typename instruction1::NOP1>(
                     this->v())) {
        return std::make_pair(0u, 0u);
      } else if (std::holds_alternative<typename instruction1::RDM>(
                     this->v())) {
        return std::make_pair(233u, 0u);
      } else if (std::holds_alternative<typename instruction1::TCS>(
                     this->v())) {
        return std::make_pair(249u, 0u);
      } else if (std::holds_alternative<typename instruction1::WPM>(
                     this->v())) {
        return std::make_pair(227u, 0u);
      } else {
        return std::make_pair(228u, 0u);
      }
    }
  };

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction1_rect(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                              F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                              const T1 f7, const T1 f8, const T1 f9,
                              const std::shared_ptr<instruction1> &i) {
    if (std::holds_alternative<typename instruction1::CLB>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instruction1::CMC>(i->v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction1::DAA>(i->v())) {
      return f1;
    } else if (std::holds_alternative<typename instruction1::FIM>(i->v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction1::FIM>(i->v());
      return f2(d_a0, d_a1);
    } else if (std::holds_alternative<typename instruction1::JUN>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction1::JUN>(i->v());
      return f3(d_a0);
    } else if (std::holds_alternative<typename instruction1::LDM1>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction1::LDM1>(i->v());
      return f4(d_a0);
    } else if (std::holds_alternative<typename instruction1::NOP1>(i->v())) {
      return f5;
    } else if (std::holds_alternative<typename instruction1::RDM>(i->v())) {
      return f6;
    } else if (std::holds_alternative<typename instruction1::TCS>(i->v())) {
      return f7;
    } else if (std::holds_alternative<typename instruction1::WPM>(i->v())) {
      return f8;
    } else {
      return f9;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, unsigned int> F3,
            MapsTo<T1, unsigned int> F4, MapsTo<T1, unsigned int> F5>
  static T1 instruction1_rec(const T1 f, const T1 f0, const T1 f1, F3 &&f2,
                             F4 &&f3, F5 &&f4, const T1 f5, const T1 f6,
                             const T1 f7, const T1 f8, const T1 f9,
                             const std::shared_ptr<instruction1> &i) {
    if (std::holds_alternative<typename instruction1::CLB>(i->v())) {
      return f;
    } else if (std::holds_alternative<typename instruction1::CMC>(i->v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction1::DAA>(i->v())) {
      return f1;
    } else if (std::holds_alternative<typename instruction1::FIM>(i->v())) {
      const auto &[d_a0, d_a1] = std::get<typename instruction1::FIM>(i->v());
      return f2(d_a0, d_a1);
    } else if (std::holds_alternative<typename instruction1::JUN>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction1::JUN>(i->v());
      return f3(d_a0);
    } else if (std::holds_alternative<typename instruction1::LDM1>(i->v())) {
      const auto &[d_a0] = std::get<typename instruction1::LDM1>(i->v());
      return f4(d_a0);
    } else if (std::holds_alternative<typename instruction1::NOP1>(i->v())) {
      return f5;
    } else if (std::holds_alternative<typename instruction1::RDM>(i->v())) {
      return f6;
    } else if (std::holds_alternative<typename instruction1::TCS>(i->v())) {
      return f7;
    } else if (std::holds_alternative<typename instruction1::WPM>(i->v())) {
      return f8;
    } else {
      return f9;
    }
  }

  __attribute__((pure)) static bool
  pair_in_range(const std::pair<unsigned int, unsigned int> p);
  static inline const bool test_encode_bytes_in_range =
      ((((((((((pair_in_range(instruction1::clb()->encode1()) &&
                pair_in_range(instruction1::cmc()->encode1())) &&
               pair_in_range(instruction1::daa()->encode1())) &&
              pair_in_range(instruction1::fim(14u, 255u)->encode1())) &&
             pair_in_range(instruction1::jun(4095u)->encode1())) &&
            pair_in_range(instruction1::ldm1(15u)->encode1())) &&
           pair_in_range(instruction1::nop1()->encode1())) &&
          pair_in_range(instruction1::rdm()->encode1())) &&
         pair_in_range(instruction1::tcs()->encode1())) &&
        pair_in_range(instruction1::wpm()->encode1())) &&
       pair_in_range(instruction1::wr0()->encode1()));

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
    explicit instruction2(NOP2 _v) : d_v_(_v) {}

    explicit instruction2(LDM2 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction2> nop2() {
      return std::make_shared<instruction2>(NOP2{});
    }

    static std::shared_ptr<instruction2> ldm2(unsigned int a0) {
      return std::make_shared<instruction2>(LDM2{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode2() const {
      if (std::holds_alternative<typename instruction2::NOP2>(this->v())) {
        return std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0] = std::get<typename instruction2::LDM2>(this->v());
        return std::make_pair(13u, (16u ? d_a0 % 16u : d_a0));
      }
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction2_rect(const T1 f, F1 &&f0,
                              const std::shared_ptr<instruction2> &i) {
    if (std::holds_alternative<typename instruction2::NOP2>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction2::LDM2>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction2_rec(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction2> &i) {
    if (std::holds_alternative<typename instruction2::NOP2>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction2::LDM2>(i->v());
      return f0(d_a0);
    }
  }

  static std::shared_ptr<List<unsigned int>> encode_list2(
      const std::shared_ptr<List<std::shared_ptr<instruction2>>> &prog);
  static inline const unsigned int test_encode_list_byte_count =
      encode_list2(List<std::shared_ptr<instruction2>>::cons(
                       instruction2::nop2(),
                       List<std::shared_ptr<instruction2>>::cons(
                           instruction2::ldm2(5u),
                           List<std::shared_ptr<instruction2>>::cons(
                               instruction2::nop2(),
                               List<std::shared_ptr<instruction2>>::nil()))))
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

  public:
    // CREATORS
    explicit instruction3(NOP3 _v) : d_v_(_v) {}

    explicit instruction3(LDM3 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<instruction3> nop3() {
      return std::make_shared<instruction3>(NOP3{});
    }

    static std::shared_ptr<instruction3> ldm3(unsigned int a0) {
      return std::make_shared<instruction3>(LDM3{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) std::pair<unsigned int, unsigned int>
    encode3() const {
      if (std::holds_alternative<typename instruction3::NOP3>(this->v())) {
        return std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0] = std::get<typename instruction3::LDM3>(this->v());
        return std::make_pair(((13u * 16u) + (16u ? d_a0 % 16u : d_a0)), 0u);
      }
    }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction3_rect(const T1 f, F1 &&f0,
                              const std::shared_ptr<instruction3> &i) {
    if (std::holds_alternative<typename instruction3::NOP3>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction3::LDM3>(i->v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction3_rec(const T1 f, F1 &&f0,
                             const std::shared_ptr<instruction3> &i) {
    if (std::holds_alternative<typename instruction3::NOP3>(i->v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction3::LDM3>(i->v());
      return f0(d_a0);
    }
  }

  static std::shared_ptr<List<unsigned int>> encode_list3(
      const std::shared_ptr<List<std::shared_ptr<instruction3>>> &prog);
  static inline const unsigned int test_instruction_byte_stream_encode =
      encode_list3(List<std::shared_ptr<instruction3>>::cons(
                       instruction3::nop3(),
                       List<std::shared_ptr<instruction3>>::cons(
                           instruction3::ldm3(3u),
                           List<std::shared_ptr<instruction3>>::cons(
                               instruction3::ldm3(12u),
                               List<std::shared_ptr<instruction3>>::nil()))))
          ->length();
  static inline const std::pair<std::pair<bool, unsigned int>, unsigned int> t =
      std::make_pair(std::make_pair(test_encode_bytes_in_range,
                                    test_encode_list_byte_count),
                     test_instruction_byte_stream_encode);
};

#endif // INCLUDED_ENCODE_OPS
