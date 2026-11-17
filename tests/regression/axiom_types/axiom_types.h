#pragma once

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
  static MysteryType use_axiom();

  struct AxiomRecord {
    uint64_t normal_field;
    MysteryType axiom_field;
  };

  static AxiomRecord make_axiom_record();
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
    return AxiomInductive_rect<T1>(f, f0, a);
  }

  static AxiomInductive use_axiom_inductive();
  static MysteryType axiom_identity(MysteryType x);
  static MysteryType nested_axiom();

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
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<list<A>>(crane_convert<list<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a0, crane::shared_child_slot<list<A>> a1) {
      return list<A>(Cons{std::move(a0), a1.take()});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
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

    template <typename T1, typename F1> T1 list_rec(T1 f, F1 &&f0) const {
      return this->template list_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 list_rect(T1 f, F1 &&f0) const {
      const list<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of list_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const list<A> *_self;
      };

      struct _after_list_rect_in_Cons {
        A a0;
        std::shared_ptr<list<A>> a1;
      };

      using _frame = std::variant<_call, _after_list_rect_in_Cons>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename list<A>::Cons>(_sv.v());
            _stack.emplace_back(_after_list_rect_in_Cons{a0, a1});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_list_rect_in_Cons>(_popped));
          _stack.pop_back();
          auto a0 = std::move(_f.a0);
          std::shared_ptr<list<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static list<MysteryType> axiom_list();

  template <typename T1> static T1 poly_axiom(T1 x) { return x; }

  static MysteryType use_poly_axiom();
};
