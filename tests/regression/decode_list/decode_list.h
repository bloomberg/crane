#ifndef INCLUDED_DECODE_LIST
#define INCLUDED_DECODE_LIST

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
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
    instruction() {}

    explicit instruction(NOP _v) : d_v_(_v) {}

    explicit instruction(LDM _v) : d_v_(std::move(_v)) {}

    instruction(const instruction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction(instruction &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) instruction &operator=(const instruction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) instruction &operator=(instruction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) instruction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP>(_sv.v())) {
        return instruction(NOP{});
      } else {
        const auto &[d_a0] = std::get<LDM>(_sv.v());
        return instruction(LDM{d_a0});
      }
    }

    // CREATORS
    constexpr static instruction nop() { return instruction(NOP{}); }

    __attribute__((pure)) static instruction ldm(unsigned int a0) {
      return instruction(LDM{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) instruction *operator->() { return this; }

    __attribute__((pure)) const instruction *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = instruction(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(const T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(const T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename instruction::LDM>(i.v());
      return f0(d_a0);
    }
  }

  __attribute__((pure)) static instruction decode(const unsigned int &b1,
                                                  const unsigned int &b2);
  __attribute__((pure)) static List<instruction>
  decode_list(const List<unsigned int> &bytes);
  static inline const unsigned int t_empty =
      decode_list(List<unsigned int>::nil()).length();
  static inline const unsigned int t_odd_tail = []() {
    auto &&_sv0 = decode_list(List<unsigned int>::cons(
        0u,
        List<unsigned int>::cons(
            99u, List<unsigned int>::cons(42u, List<unsigned int>::nil()))));
    if (std::holds_alternative<typename List<instruction>::Nil>(_sv0.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<instruction>::Cons>(_sv0.v());
      if (std::holds_alternative<typename instruction::NOP>(d_a00.v())) {
        auto &&_sv = *(d_a10);
        if (std::holds_alternative<typename List<instruction>::Nil>(_sv.v())) {
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
          .length();
  static inline const unsigned int t_single_pair =
      decode_list(
          List<unsigned int>::cons(
              0u, List<unsigned int>::cons(7u, List<unsigned int>::nil())))
          .length();
};

#endif // INCLUDED_DECODE_LIST
