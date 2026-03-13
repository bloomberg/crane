#ifndef INCLUDED_RECORD_CASE_BODY
#define INCLUDED_RECORD_CASE_BODY

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

  __attribute__((pure)) static unsigned int
  case_in_body(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int helper(const unsigned int n);
  __attribute__((pure)) static unsigned int
  fix_in_body(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  let_in_body(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  apply_nonfld(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  conditional_body(const std::shared_ptr<Rec> &r, const bool flag);
  __attribute__((pure)) static unsigned int
  outer_ref(const unsigned int x, const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  lambda_body(const std::shared_ptr<Rec> &r, const unsigned int n);

  struct RecRec {
    std::shared_ptr<Rec> inner;
    unsigned int outer_field;
  };

  __attribute__((pure)) static unsigned int
  nested_record_match(const std::shared_ptr<RecRec> &rr);
  static inline const unsigned int global_const = 42u;
  __attribute__((pure)) static unsigned int
  global_in_body(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  guarded_body(const std::shared_ptr<Rec> &r);
  static std::shared_ptr<Rec> constructor_body(const std::shared_ptr<Rec> &r);

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  __attribute__((pure)) static unsigned int
  sum_list(const std::shared_ptr<list<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  list_in_body(const std::shared_ptr<Rec> &r);
  static inline const unsigned int test1 =
      case_in_body(std::make_shared<Rec>(Rec{1u, 2u, 3u}));
  static inline const unsigned int test2 =
      fix_in_body(std::make_shared<Rec>(Rec{4u, 5u, 6u}));
  static inline const unsigned int test3 =
      let_in_body(std::make_shared<Rec>(Rec{0u, 1u, 2u}));
};

#endif // INCLUDED_RECORD_CASE_BODY
