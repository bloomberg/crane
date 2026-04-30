#ifndef INCLUDED_RECORD_CASE_BODY
#define INCLUDED_RECORD_CASE_BODY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordCaseBody {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;

    // ACCESSORS
    Rec clone() const { return Rec{(*(this)).f1, (*(this)).f2, (*(this)).f3}; }
  };

  static unsigned int case_in_body(const Rec &r);
  static unsigned int helper(const unsigned int &n);
  static unsigned int fix_in_body(const Rec &r);
  static unsigned int let_in_body(const Rec &r);
  static unsigned int apply_nonfld(const Rec &r);
  static unsigned int conditional_body(const Rec &r, const bool &flag);
  static unsigned int outer_ref(const unsigned int &x, const Rec &r);
  static unsigned int lambda_body(const Rec &r, const unsigned int &n);

  struct RecRec {
    Rec inner;
    unsigned int outer_field;

    // ACCESSORS
    RecRec clone() const {
      return RecRec{(*(this)).inner.clone(), (*(this)).outer_field};
    }
  };

  static unsigned int nested_record_match(const RecRec &rr);
  static inline const unsigned int global_const = 42u;
  static unsigned int global_in_body(const Rec &r);
  static unsigned int guarded_body(const Rec &r);
  static Rec constructor_body(const Rec &r);

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
    list clone() const {
      list _out{};

      struct _CloneFrame {
        const list *_src;
        list *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list *_src = _frame._src;
        list *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          const auto &_alt = std::get<Nil>(_src->v());
          _dst->d_v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->d_v_ =
              Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<list>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
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

    static list<t_A> nil() { return list(Nil{}); }

    static list<t_A> cons(t_A a0, list<t_A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list>> _stack;
      auto _drain = [&](list &_node) {
        if (std::holds_alternative<Cons>(_node.d_v_)) {
          auto &_alt = std::get<Cons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

  static unsigned int sum_list(const list<unsigned int> &l);
  static unsigned int list_in_body(const Rec &r);
  static inline const unsigned int test1 = case_in_body(Rec{1u, 2u, 3u});
  static inline const unsigned int test2 = fix_in_body(Rec{4u, 5u, 6u});
  static inline const unsigned int test3 = let_in_body(Rec{0u, 1u, 2u});
};

#endif // INCLUDED_RECORD_CASE_BODY
