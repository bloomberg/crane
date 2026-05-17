#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
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

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated UNIQUE sorting algorithms and related operations.
struct LoopifySorting {
  template <typename T1>
  static uint64_t
  len_impl(const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified len_impl: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  static List<uint64_t> insert(uint64_t x, List<uint64_t> l);
  static List<uint64_t> insertion_sort(const List<uint64_t> &l);

  template <typename T1>
  static std::pair<List<T1>, List<T1>>
  split(const List<T1> &l) { /// _Enter: captures varying parameters for each
                             /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Cont_Cons: saves [a0, a00], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      T1 a0;
      T1 a00;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified split: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(List<T1>::cons(a0, List<T1>::nil()),
                                     List<T1>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Cont_Cons{a0, a00});
            _stack.emplace_back(_Enter{a10.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        T1 a0 = _f.a0;
        T1 a00 = _f.a00;
        const List<T1> &l1 = _result.first;
        const List<T1> &l2 = _result.second;
        _result =
            std::make_pair(List<T1>::cons(a0, l1), List<T1>::cons(a00, l2));
      }
    }
    return _result;
  }

  static List<uint64_t> merge_fuel(uint64_t fuel, List<uint64_t> l1,
                                   List<uint64_t> l2);
  static List<uint64_t> merge(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static List<uint64_t> merge_sort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> merge_sort(const List<uint64_t> &l);
  static std::pair<List<uint64_t>, List<uint64_t>>
  partition(uint64_t pivot, const List<uint64_t> &l);
  static List<uint64_t> quicksort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> quicksort(const List<uint64_t> &l);
  static bool is_sorted_aux(uint64_t prev, const List<uint64_t> &l);
  static bool is_sorted(const List<uint64_t> &l);

  /// merge_by cmp merges with custom comparator.
  template <typename F1>
    requires std::is_invocable_r_v<bool, F1 &, uint64_t &, uint64_t &>
  static List<uint64_t> merge_by_fuel(uint64_t fuel, F1 &&cmp,
                                      List<uint64_t> l1, List<uint64_t> l2) {
    if (fuel <= 0) {
      return List<uint64_t>::nil();
    } else {
      uint64_t f = fuel - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
        return l2;
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v_mut())) {
          return l1;
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v_mut());
          if (cmp(a0, a00)) {
            return List<uint64_t>::cons(std::move(a0),
                                        merge_by_fuel(f, cmp, *a1, l2));
          } else {
            return List<uint64_t>::cons(std::move(a00),
                                        merge_by_fuel(f, cmp, l1, *a10));
          }
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &>
  static List<uint64_t> merge_by(F0 &&cmp, const List<uint64_t> &l1,
                                 const List<uint64_t> &l2) {
    return merge_by_fuel((len_impl<uint64_t>(l1) + len_impl<uint64_t>(l2)), cmp,
                         l1, l2);
  }

  /// remove_duplicates removes consecutive duplicates from sorted list.
  static List<uint64_t> remove_duplicates(const List<uint64_t> &l);
  /// uniq_sorted variant that preserves order.
  static List<uint64_t> uniq_sorted_aux(uint64_t prev, bool seen,
                                        const List<uint64_t> &l);
  static List<uint64_t> uniq_sorted(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_SORTING
