#ifndef INCLUDED_RECORD_CASE_BODY
#define INCLUDED_RECORD_CASE_BODY

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct RecordCaseBody {
  struct Rec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;
  };

  static uint64_t case_in_body(const Rec &r);
  static uint64_t helper(uint64_t n);
  static uint64_t fix_in_body(const Rec &r);
  static uint64_t let_in_body(const Rec &r);
  static uint64_t apply_nonfld(const Rec &r);
  static uint64_t conditional_body(const Rec &r, bool flag);
  static uint64_t outer_ref(uint64_t x, const Rec &r);
  static uint64_t lambda_body(const Rec &r, uint64_t n);

  struct RecRec {
    Rec inner;
    uint64_t outer_field;
  };

  static uint64_t nested_record_match(const RecRec &rr);
  static constexpr uint64_t global_const = UINT64_C(42);
  static uint64_t global_in_body(const Rec &r);
  static uint64_t guarded_body(const Rec &r);
  static Rec constructor_body(const Rec &r);

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
                  (a1 ? std::make_shared<list<A>>(crane_convert<list<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

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
  };

  template <typename T1, typename T2, typename F1>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(const T2 &f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(f, f0, l);
  }

  static uint64_t sum_list(const list<uint64_t> &l);
  static uint64_t list_in_body(const Rec &r);
  static constexpr uint64_t test1 = UINT64_C(5);
  static constexpr uint64_t test2 = UINT64_C(120);
  static constexpr uint64_t test3 = UINT64_C(6);
};

#endif // INCLUDED_RECORD_CASE_BODY
