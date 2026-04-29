#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
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
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = std::move(_next_self);
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated UNIQUE sorting algorithms and related operations.
struct LoopifySorting {
  template <typename T1>
  __attribute__((pure)) static unsigned int len_impl(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  __attribute__((pure)) static List<unsigned int> insert(unsigned int x,
                                                         List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  insertion_sort(const List<unsigned int> &l);

  template <typename T1>
  __attribute__((pure)) static std::pair<List<T1>, List<T1>>
  split(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {
      T1 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<List<T1>, List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = std::make_pair(List<T1>::nil(), List<T1>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
            _result = std::make_pair(List<T1>::cons(d_a0, List<T1>::nil()),
                                     List<T1>::nil());
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<T1>::Cons>(_sv0.v());
            _stack.emplace_back(_Call1{d_a0, d_a00});
            _stack.emplace_back(_Enter{*(d_a10)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        T1 d_a0 = _f._s0;
        T1 d_a00 = _f._s1;
        const List<T1> &l1 = _result.first;
        const List<T1> &l2 = _result.second;
        _result =
            std::make_pair(List<T1>::cons(d_a0, l1), List<T1>::cons(d_a00, l2));
      }
    }
    return _result;
  }

  __attribute__((pure)) static List<unsigned int>
  merge_fuel(const unsigned int &fuel, List<unsigned int> l1,
             List<unsigned int> l2);
  __attribute__((pure)) static List<unsigned int>
  merge(const List<unsigned int> &l1, const List<unsigned int> &l2);
  __attribute__((pure)) static List<unsigned int>
  merge_sort_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  merge_sort(const List<unsigned int> &l);
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  partition(const unsigned int &pivot, const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  quicksort_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  quicksort(const List<unsigned int> &l);
  __attribute__((pure)) static bool is_sorted_aux(const unsigned int &prev,
                                                  const List<unsigned int> &l);
  __attribute__((pure)) static bool
  is_sorted(const List<unsigned int>
                &l); /// merge_by cmp merges with custom comparator.

  template <MapsTo<bool, unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<unsigned int>
  merge_by_fuel(const unsigned int &fuel, F1 &&cmp, List<unsigned int> l1,
                List<unsigned int> l2) {
    if (fuel <= 0) {
      return List<unsigned int>::nil();
    } else {
      unsigned int f = fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              l1.v_mut())) {
        return l2;
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l2.v_mut())) {
          return l1;
        } else {
          auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(l2.v_mut());
          if (cmp(d_a0, d_a00)) {
            return List<unsigned int>::cons(d_a0,
                                            merge_by_fuel(f, cmp, *(d_a1), l2));
          } else {
            return List<unsigned int>::cons(
                d_a00, merge_by_fuel(f, cmp, l1, *(d_a10)));
          }
        }
      }
    }
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  merge_by(F0 &&cmp, const List<unsigned int> &l1,
           const List<unsigned int> &l2) {
    return merge_by_fuel(
        (len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)), cmp, l1, l2);
  }

  /// remove_duplicates removes consecutive duplicates from sorted list.
  __attribute__((pure)) static List<unsigned int>
  remove_duplicates(const List<unsigned int> &l);
  /// uniq_sorted variant that preserves order.
  __attribute__((pure)) static List<unsigned int>
  uniq_sorted_aux(const unsigned int &prev, const bool &seen,
                  const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  uniq_sorted(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_SORTING
