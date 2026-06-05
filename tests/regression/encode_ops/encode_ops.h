#ifndef INCLUDED_ENCODE_OPS
#define INCLUDED_ENCODE_OPS

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
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
      uint64_t a0;
      uint64_t a1;
    };

    struct JUN {
      uint64_t a0;
    };

    struct LDM1 {
      uint64_t a0;
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
    variant_t v_;

  public:
    // CREATORS
    instruction1() {}

    explicit instruction1(CLB _v) : v_(_v) {}

    explicit instruction1(CMC _v) : v_(_v) {}

    explicit instruction1(DAA _v) : v_(_v) {}

    explicit instruction1(FIM _v) : v_(std::move(_v)) {}

    explicit instruction1(JUN _v) : v_(std::move(_v)) {}

    explicit instruction1(LDM1 _v) : v_(std::move(_v)) {}

    explicit instruction1(NOP1 _v) : v_(_v) {}

    explicit instruction1(RDM _v) : v_(_v) {}

    explicit instruction1(TCS _v) : v_(_v) {}

    explicit instruction1(WPM _v) : v_(_v) {}

    explicit instruction1(WR0 _v) : v_(_v) {}

    static instruction1 clb() { return instruction1(CLB{}); }

    static instruction1 cmc() { return instruction1(CMC{}); }

    static instruction1 daa() { return instruction1(DAA{}); }

    static instruction1 fim(uint64_t a0, uint64_t a1) {
      return instruction1(FIM{a0, a1});
    }

    static instruction1 jun(uint64_t a0) { return instruction1(JUN{a0}); }

    static instruction1 ldm1(uint64_t a0) { return instruction1(LDM1{a0}); }

    static instruction1 nop1() { return instruction1(NOP1{}); }

    static instruction1 rdm() { return instruction1(RDM{}); }

    static instruction1 tcs() { return instruction1(TCS{}); }

    static instruction1 wpm() { return instruction1(WPM{}); }

    static instruction1 wr0() { return instruction1(WR0{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::pair<uint64_t, uint64_t> encode1() const {
      if (std::holds_alternative<typename instruction1::CLB>(this->v())) {
        return std::make_pair(UINT64_C(240), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::CMC>(
                     this->v())) {
        return std::make_pair(UINT64_C(243), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::DAA>(
                     this->v())) {
        return std::make_pair(UINT64_C(251), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::FIM>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::FIM>(this->v());
        return std::make_pair(
            (UINT64_C(32) +
             (((a0 - (UINT64_C(2) ? a0 % UINT64_C(2) : a0)) > a0
                   ? 0
                   : (a0 - (UINT64_C(2) ? a0 % UINT64_C(2) : a0))))),
            (UINT64_C(256) ? a1 % UINT64_C(256) : a1));
      } else if (std::holds_alternative<typename instruction1::JUN>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::JUN>(this->v());
        return std::make_pair(
            (UINT64_C(64) + (UINT64_C(256) ? a0 / UINT64_C(256) : 0)),
            (UINT64_C(256) ? a0 % UINT64_C(256) : a0));
      } else if (std::holds_alternative<typename instruction1::LDM1>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::LDM1>(this->v());
        return std::make_pair(
            (UINT64_C(208) + (UINT64_C(16) ? a0 % UINT64_C(16) : a0)),
            UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::NOP1>(
                     this->v())) {
        return std::make_pair(UINT64_C(0), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::RDM>(
                     this->v())) {
        return std::make_pair(UINT64_C(233), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::TCS>(
                     this->v())) {
        return std::make_pair(UINT64_C(249), UINT64_C(0));
      } else if (std::holds_alternative<typename instruction1::WPM>(
                     this->v())) {
        return std::make_pair(UINT64_C(227), UINT64_C(0));
      } else {
        return std::make_pair(UINT64_C(228), UINT64_C(0));
      }
    }

    template <typename T1, typename F3, typename F4, typename F5>
      requires std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &>
    T1 instruction1_rec(T1 f, T1 f0, T1 f1, F3 &&f2, F4 &&f3, F5 &&f4, T1 f5,
                        T1 f6, T1 f7, T1 f8, T1 f9) const {
      if (std::holds_alternative<typename instruction1::CLB>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instruction1::CMC>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<typename instruction1::DAA>(
                     this->v())) {
        return f1;
      } else if (std::holds_alternative<typename instruction1::FIM>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::FIM>(this->v());
        return f2(a0, a1);
      } else if (std::holds_alternative<typename instruction1::JUN>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::JUN>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instruction1::LDM1>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::LDM1>(this->v());
        return f4(a0);
      } else if (std::holds_alternative<typename instruction1::NOP1>(
                     this->v())) {
        return f5;
      } else if (std::holds_alternative<typename instruction1::RDM>(
                     this->v())) {
        return f6;
      } else if (std::holds_alternative<typename instruction1::TCS>(
                     this->v())) {
        return f7;
      } else if (std::holds_alternative<typename instruction1::WPM>(
                     this->v())) {
        return f8;
      } else {
        return f9;
      }
    }

    template <typename T1, typename F3, typename F4, typename F5>
      requires std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &> &&
               std::is_invocable_r_v<T1, F4 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F5 &, uint64_t &>
    T1 instruction1_rect(T1 f, T1 f0, T1 f1, F3 &&f2, F4 &&f3, F5 &&f4, T1 f5,
                         T1 f6, T1 f7, T1 f8, T1 f9) const {
      if (std::holds_alternative<typename instruction1::CLB>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename instruction1::CMC>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<typename instruction1::DAA>(
                     this->v())) {
        return f1;
      } else if (std::holds_alternative<typename instruction1::FIM>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename instruction1::FIM>(this->v());
        return f2(a0, a1);
      } else if (std::holds_alternative<typename instruction1::JUN>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::JUN>(this->v());
        return f3(a0);
      } else if (std::holds_alternative<typename instruction1::LDM1>(
                     this->v())) {
        const auto &[a0] = std::get<typename instruction1::LDM1>(this->v());
        return f4(a0);
      } else if (std::holds_alternative<typename instruction1::NOP1>(
                     this->v())) {
        return f5;
      } else if (std::holds_alternative<typename instruction1::RDM>(
                     this->v())) {
        return f6;
      } else if (std::holds_alternative<typename instruction1::TCS>(
                     this->v())) {
        return f7;
      } else if (std::holds_alternative<typename instruction1::WPM>(
                     this->v())) {
        return f8;
      } else {
        return f9;
      }
    }
  };

  static bool pair_in_range(const std::pair<uint64_t, uint64_t> &p);
  static inline const bool test_encode_bytes_in_range =
      ((((((((((pair_in_range(instruction1::clb().encode1()) &&
                pair_in_range(instruction1::cmc().encode1())) &&
               pair_in_range(instruction1::daa().encode1())) &&
              pair_in_range(
                  instruction1::fim(UINT64_C(14), UINT64_C(255)).encode1())) &&
             pair_in_range(instruction1::jun(UINT64_C(4095)).encode1())) &&
            pair_in_range(instruction1::ldm1(UINT64_C(15)).encode1())) &&
           pair_in_range(instruction1::nop1().encode1())) &&
          pair_in_range(instruction1::rdm().encode1())) &&
         pair_in_range(instruction1::tcs().encode1())) &&
        pair_in_range(instruction1::wpm().encode1())) &&
       pair_in_range(instruction1::wr0().encode1()));

  struct instruction2 {
    // TYPES
    struct NOP2 {};

    struct LDM2 {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP2, LDM2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction2() {}

    explicit instruction2(NOP2 _v) : v_(_v) {}

    explicit instruction2(LDM2 _v) : v_(std::move(_v)) {}

    static instruction2 nop2() { return instruction2(NOP2{}); }

    static instruction2 ldm2(uint64_t a0) { return instruction2(LDM2{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::pair<uint64_t, uint64_t> encode2() const {
      if (std::holds_alternative<typename instruction2::NOP2>(this->v())) {
        return std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0] = std::get<typename instruction2::LDM2>(this->v());
        return std::make_pair(UINT64_C(13),
                              (UINT64_C(16) ? a0 % UINT64_C(16) : a0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instruction2_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename instruction2::NOP2>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename instruction2::LDM2>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instruction2_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename instruction2::NOP2>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename instruction2::LDM2>(this->v());
        return f0(a0);
      }
    }
  };

  static List<uint64_t> encode_list2(const List<instruction2> &prog);
  static inline const uint64_t test_encode_list_byte_count =
      encode_list2(
          List<instruction2>::cons(
              instruction2::nop2(),
              List<instruction2>::cons(
                  instruction2::ldm2(UINT64_C(5)),
                  List<instruction2>::cons(instruction2::nop2(),
                                           List<instruction2>::nil()))))
          .length();

  struct instruction3 {
    // TYPES
    struct NOP3 {};

    struct LDM3 {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP3, LDM3>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction3() {}

    explicit instruction3(NOP3 _v) : v_(_v) {}

    explicit instruction3(LDM3 _v) : v_(std::move(_v)) {}

    static instruction3 nop3() { return instruction3(NOP3{}); }

    static instruction3 ldm3(uint64_t a0) { return instruction3(LDM3{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    std::pair<uint64_t, uint64_t> encode3() const {
      if (std::holds_alternative<typename instruction3::NOP3>(this->v())) {
        return std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0] = std::get<typename instruction3::LDM3>(this->v());
        return std::make_pair(((UINT64_C(13) * UINT64_C(16)) +
                               (UINT64_C(16) ? a0 % UINT64_C(16) : a0)),
                              UINT64_C(0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instruction3_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename instruction3::NOP3>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename instruction3::LDM3>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
    T1 instruction3_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename instruction3::NOP3>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename instruction3::LDM3>(this->v());
        return f0(a0);
      }
    }
  };

  static List<uint64_t> encode_list3(const List<instruction3> &prog);
  static inline const uint64_t test_instruction_byte_stream_encode =
      encode_list3(
          List<instruction3>::cons(
              instruction3::nop3(),
              List<instruction3>::cons(
                  instruction3::ldm3(UINT64_C(3)),
                  List<instruction3>::cons(instruction3::ldm3(UINT64_C(12)),
                                           List<instruction3>::nil()))))
          .length();

  static inline const std::pair<std::pair<bool, uint64_t>, uint64_t> t =
      std::make_pair(std::make_pair(test_encode_bytes_in_range,
                                    test_encode_list_byte_count),
                     test_instruction_byte_stream_encode);
};

#endif // INCLUDED_ENCODE_OPS
