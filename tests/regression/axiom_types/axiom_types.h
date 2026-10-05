#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct AxiomTypes {
  using MysteryType = crane::obj /* AXIOM TO BE REALIZED */;
  static MysteryType mystery_value();
  static MysteryType mystery_function(MysteryType x0_);
  static MysteryType use_axiom(std::monostate _x);

  struct AxiomRecord {
    uint64_t normal_field;
    MysteryType axiom_field;
  };

  static AxiomRecord make_axiom_record(std::monostate _x);
  static MysteryType extract_axiom_field(const AxiomRecord &r);

  struct AxiomInductive {
    // TYPES
    struct AxConstr1 {
      uint64_t a0;
    };

    struct AxConstr2 {
      MysteryType a0;
    };

    using variant_t = std::variant<AxConstr1, AxConstr2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    AxiomInductive() {}

    explicit AxiomInductive(AxConstr1 _v) : v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : v_(std::move(_v)) {}

    static AxiomInductive axconstr1(uint64_t a0) {
      return AxiomInductive(AxConstr1{a0});
    }

    static AxiomInductive axconstr2(MysteryType a0) {
      return AxiomInductive(AxConstr2{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return crane_call_erased(f0, a0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    return AxiomInductive_rect<T1>(f, crane_erase_fn<T1>(f0), a);
  }

  static AxiomInductive use_axiom_inductive(std::monostate _x);
  static MysteryType axiom_identity(MysteryType x);
  static MysteryType nested_axiom(std::monostate _x);

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<list<A>>(nullptr),
              [](const list<CraneU> &_cell) -> const list<CraneU> * {
                if (std::holds_alternative<typename list<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename list<CraneU>::Cons>(_cell.v())
                      .a1.get();
                } else {
                  return nullptr;
                }
              },
              [&](const list<CraneU> &_other,
                  std::shared_ptr<list<A>> _below) -> variant_t {
                if (std::holds_alternative<typename list<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a0, a1] =
                      std::get<typename list<CraneU>::Cons>(_other.v());
                  return Cons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
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
                return std::make_shared<list<A>>(std::move(_alt));
              })) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list<A>(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
    T1 list_rec(const T1 &f, F1 &&f0) const {
      return this->template list_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 list_rect(T1 f, F1 &&f0) const {
      const list<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const list<A> *_self;
      };

      /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Cons {
        A a0;
        std::shared_ptr<list<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified list_rect: CraneEnter -> CraneCont_Cons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename list<A>::Cons>(_sv.v());
            _stack.emplace_back(CraneCont_Cons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Cons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<list<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static list<MysteryType> axiom_list(std::monostate _x);

  template <typename T1> static T1 poly_axiom(T1 x) { return x; }

  static MysteryType use_poly_axiom(std::monostate _x);
};

#endif // INCLUDED_AXIOM_TYPES
