#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordCaseBody {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;
  };

  static unsigned int case_in_body(const std::shared_ptr<Rec> &r);
  static unsigned int helper(const unsigned int n);
  static unsigned int fix_in_body(const std::shared_ptr<Rec> &r);
  static unsigned int let_in_body(const std::shared_ptr<Rec> &r);
  static unsigned int apply_nonfld(const std::shared_ptr<Rec> &r);
  static unsigned int conditional_body(const std::shared_ptr<Rec> &r,
                                       const bool flag);
  static unsigned int outer_ref(const unsigned int x,
                                const std::shared_ptr<Rec> &r);
  static unsigned int lambda_body(const std::shared_ptr<Rec> &r,
                                  const unsigned int n);

  struct RecRec {
    std::shared_ptr<Rec> inner;
    unsigned int outer_field;
  };

  static unsigned int nested_record_match(const std::shared_ptr<RecRec> &rr);
  static inline const unsigned int global_const = 42u;
  static unsigned int global_in_body(const std::shared_ptr<Rec> &r);
  static unsigned int guarded_body(const std::shared_ptr<Rec> &r);
  static std::shared_ptr<Rec> constructor_body(const std::shared_ptr<Rec> &r);

  template <typename A> struct list {
    // TYPES
    struct nil {};

    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };

    using variant_t = std::variant<nil, cons>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit list(nil _v) : v_(std::move(_v)) {}

    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }

      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }

      static std::unique_ptr<list<A>> nil_uptr() {
        return std::unique_ptr<list<A>>(new list<A>(nil{}));
      }

      static std::unique_ptr<list<A>>
      cons_uptr(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::unique_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  static unsigned int sum_list(const std::shared_ptr<list<unsigned int>> &l);
  static unsigned int list_in_body(const std::shared_ptr<Rec> &r);
  static inline const unsigned int test1 =
      case_in_body(std::make_shared<Rec>(Rec{1u, 2u, 3u}));
  static inline const unsigned int test2 =
      fix_in_body(std::make_shared<Rec>(Rec{4u, 5u, 6u}));
  static inline const unsigned int test3 =
      let_in_body(std::make_shared<Rec>(Rec{0u, 1u, 2u}));
};
