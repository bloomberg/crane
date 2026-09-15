#ifndef INCLUDED_DECL_ORDER_ALIAS_RECORD
#define INCLUDED_DECL_ORDER_ALIAS_RECORD

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
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

  template <typename _U> Instr(const Instr<_U> &_other) {
    if (std::holds_alternative<typename Instr<_U>::IGo>(_other.v())) {
      const auto &[a0] = std::get<typename Instr<_U>::IGo>(_other.v());
      this->v_ = IGo{[&]() -> target {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<target>(a0);
        } else {
          return target(a0);
        }
      }()};
    } else {
      if (std::holds_alternative<typename Instr<_U>::ICmp>(_other.v())) {
        const auto &[a0] = std::get<typename Instr<_U>::ICmp>(_other.v());
        this->v_ = ICmp{a0};
      } else {
        this->v_ = IStop{};
      }
    }
  }

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

const prog sample =
    prog{List<Instr<uint64_t>>::cons(
             Instr<uint64_t>::igo(UINT64_C(3)),
             List<Instr<uint64_t>>::cons(
                 Instr<uint64_t>::icmp(Cop::CEQ),
                 List<Instr<uint64_t>>::cons(Instr<uint64_t>::istop(),
                                             List<Instr<uint64_t>>::nil()))),
         UINT64_C(2)};
const uint64_t sample_size = sample.code.length();
const uint64_t sample_regs = sample.nregs;

#endif // INCLUDED_DECL_ORDER_ALIAS_RECORD
