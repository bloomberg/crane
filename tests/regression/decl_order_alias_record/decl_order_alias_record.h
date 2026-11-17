#ifndef INCLUDED_DECL_ORDER_ALIAS_RECORD
#define INCLUDED_DECL_ORDER_ALIAS_RECORD

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
enum class Cop;
template <typename target> struct Instr;
struct prog;

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

enum class Cop { CEQ, CLT };

template <typename target> struct Instr {
  // TYPES
  struct IGo {
    target a0;
  };

  struct ICmp {
    Cop a0;
  };

  struct IStop {};

  using variant_t = std::variant<IGo, ICmp, IStop>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Instr() {}

  explicit Instr(IGo _v) : v_(std::move(_v)) {}

  explicit Instr(ICmp _v) : v_(std::move(_v)) {}

  explicit Instr(IStop _v) : v_(_v) {}

  template <typename CraneU>
  Instr(const Instr<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Instr<CraneU>::IGo>(_other.v())) {
            const auto &[a0] =
                std::get<typename Instr<CraneU>::IGo>(_other.v());
            return IGo{[&]() -> target {
              if constexpr (crane_convertible<target, const CraneU &>) {
                return crane_convert<target>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            if (std::holds_alternative<typename Instr<CraneU>::ICmp>(_other.v())) {
              const auto &[a0] =
                  std::get<typename Instr<CraneU>::ICmp>(_other.v());
              return ICmp{a0};
            } else {
              return IStop{};
            }
          }
        }()) {}

  static Instr<target> igo(target a0) {
    return Instr<target>(IGo{std::move(a0)});
  }

  static Instr<target> icmp(Cop a0) { return Instr<target>(ICmp{a0}); }

  static Instr<target> istop() { return Instr<target>(IStop{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using final_instr = Instr<uint64_t>;

struct prog {
  List<final_instr> code;
  uint64_t nregs;
};

const prog sample = prog{List<Instr<uint64_t>>::cons(
    Instr<uint64_t>::igo(UINT64_C(3)),
    List<Instr<uint64_t>>::cons(
        Instr<uint64_t>::icmp(Cop::CEQ),
        List<Instr<uint64_t>>::cons(Instr<uint64_t>::istop(),
                                    List<Instr<uint64_t>>::nil()))),
                         UINT64_C(2)};
const uint64_t sample_size = sample.code.length();
const uint64_t sample_regs = sample.nregs;

#endif // INCLUDED_DECL_ORDER_ALIAS_RECORD
