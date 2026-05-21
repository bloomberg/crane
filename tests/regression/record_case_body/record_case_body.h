#ifndef INCLUDED_RECORD_CASE_BODY
#define INCLUDED_RECORD_CASE_BODY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct RecordCaseBody {
  struct Rec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;

    // ACCESSORS
    Rec clone() const { return Rec{this->f1, this->f2, this->f3}; }
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

    // ACCESSORS
    RecRec clone() const {
      return RecRec{this->inner.clone(), this->outer_field};
    }
  };

  static uint64_t nested_record_match(const RecRec &rr);
  static inline const uint64_t global_const = UINT64_C(42);
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

    list(const list<A> &_other) : v_(std::move(_other.clone().v_)) {}

    list(list<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    list<A> &operator=(const list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list<A> &operator=(list<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    list<A> clone() const {
      list<A> _out{};

      struct _CloneFrame {
        const list<A> *_src;
        list<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<A> *_src = _frame._src;
        list<A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->v_ =
              Cons{_alt.a0, _alt.a1 ? std::make_shared<list<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a0), a1 ? std::make_shared<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<A> &_node) {
        if (std::holds_alternative<Cons>(_node.v_)) {
          auto &_alt = std::get<Cons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(f, f0, *a1));
    }
  }

  static uint64_t sum_list(const list<uint64_t> &l);
  static uint64_t list_in_body(const Rec &r);
  static inline const uint64_t test1 =
      case_in_body(Rec{UINT64_C(1), UINT64_C(2), UINT64_C(3)});
  static inline const uint64_t test2 =
      fix_in_body(Rec{UINT64_C(4), UINT64_C(5), UINT64_C(6)});
  static inline const uint64_t test3 =
      let_in_body(Rec{UINT64_C(0), UINT64_C(1), UINT64_C(2)});
};

#endif // INCLUDED_RECORD_CASE_BODY
