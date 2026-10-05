#ifndef INCLUDED_PROGRAM_WF
#define INCLUDED_PROGRAM_WF

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ProgramWf {
  struct instruction {
    // TYPES
    struct JUN {
      uint64_t a0;
    };

    struct JMS {
      uint64_t a0;
    };

    struct NOP {};

    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(JUN _v) : v_(std::move(_v)) {}

    explicit instruction(JMS _v) : v_(std::move(_v)) {}

    explicit instruction(NOP _v) : v_(_v) {}

    static instruction jun(uint64_t a0) { return instruction(JUN{a0}); }

    static instruction jms(uint64_t a0) { return instruction(JMS{a0}); }

    static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const uint64_t &>
  static T1 instruction_rect(F0 &&f, F1 &&f0, T1 f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::JUN>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JUN>(i.v());
      return f(a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JMS>(i.v());
      return f0(a0);
    } else {
      return f1;
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 &f1,
                            const instruction &i) {
    return instruction_rect<T1>(f, f0, f1, i);
  }

  struct layout {
    uint64_t base_addr;
    uint64_t code_size;
  };

  static std::optional<uint64_t> jump_target(const instruction &i);
  static inline const layout sample_layout =
      layout{UINT64_C(200), UINT64_C(20)};
  static inline const List<instruction> sample_prog = List<instruction>::cons(
      instruction::nop(),
      List<instruction>::cons(
          instruction::jun(UINT64_C(205)),
          List<instruction>::cons(instruction::jms(UINT64_C(218)),
                                  List<instruction>::nil())));
  static constexpr uint64_t sample_code_size = UINT64_C(20);
};

#endif // INCLUDED_PROGRAM_WF
