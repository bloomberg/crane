#ifndef INCLUDED_RECORD_CASE_BODY
#define INCLUDED_RECORD_CASE_BODY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordCaseBody {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;

    __attribute__((pure)) Rec *operator->() { return this; }

    __attribute__((pure)) const Rec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rec clone() const {
      return Rec{(*(this)).f1, (*(this)).f2, (*(this)).f3};
    }
  };

  __attribute__((pure)) static unsigned int case_in_body(const Rec &r);
  __attribute__((pure)) static unsigned int helper(const unsigned int &n);
  __attribute__((pure)) static unsigned int fix_in_body(const Rec &r);
  __attribute__((pure)) static unsigned int let_in_body(const Rec &r);
  __attribute__((pure)) static unsigned int apply_nonfld(const Rec &r);
  __attribute__((pure)) static unsigned int conditional_body(const Rec &r,
                                                             const bool &flag);
  __attribute__((pure)) static unsigned int outer_ref(const unsigned int &x,
                                                      const Rec &r);
  __attribute__((pure)) static unsigned int lambda_body(const Rec &r,
                                                        const unsigned int &n);

  struct RecRec {
    Rec inner;
    unsigned int outer_field;

    __attribute__((pure)) RecRec *operator->() { return this; }

    __attribute__((pure)) const RecRec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) RecRec clone() const {
      return RecRec{(*(this)).inner.clone(), (*(this)).outer_field};
    }
  };

  __attribute__((pure)) static unsigned int
  nested_record_match(const RecRec &rr);
  static inline const unsigned int global_const = 42u;
  __attribute__((pure)) static unsigned int global_in_body(const Rec &r);
  __attribute__((pure)) static unsigned int guarded_body(const Rec &r);
  __attribute__((pure)) static Rec constructor_body(const Rec &r);

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0,
            d_a1 ? std::make_unique<RecordCaseBody::list<t_A>>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(d_a0, *(d_a1), list_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  __attribute__((pure)) static unsigned int
  sum_list(const list<unsigned int> &l);
  __attribute__((pure)) static unsigned int list_in_body(const Rec &r);
  static inline const unsigned int test1 = case_in_body(Rec{1u, 2u, 3u});
  static inline const unsigned int test2 = fix_in_body(Rec{4u, 5u, 6u});
  static inline const unsigned int test3 = let_in_body(Rec{0u, 1u, 2u});
};

#endif // INCLUDED_RECORD_CASE_BODY
