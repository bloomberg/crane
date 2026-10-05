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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
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
            if (std::holds_alternative<typename Instr<CraneU>::ICmp>(
                    _other.v())) {
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

const prog sample =
    prog{List<Instr<uint64_t>>::cons(
             Instr<uint64_t>::igo(UINT64_C(3)),
             List<Instr<uint64_t>>::cons(
                 Instr<uint64_t>::icmp(Cop::CEQ),
                 List<Instr<uint64_t>>::cons(Instr<uint64_t>::istop(),
                                             List<Instr<uint64_t>>::nil()))),
         UINT64_C(2)};
inline constexpr uint64_t sample_size = UINT64_C(3);
inline constexpr uint64_t sample_regs = UINT64_C(2);

#endif // INCLUDED_DECL_ORDER_ALIAS_RECORD
