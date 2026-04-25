#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
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
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    List<unsigned int> _loop_l2 = std::move(l2);
    List<unsigned int> _loop_l1 = std::move(l1);
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l1.v())) {
          *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _loop_l2.v())) {
            *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
            if (cmp(d_a0, d_a00)) {
              auto _cell = std::make_unique<List<unsigned int>>(
                  typename List<unsigned int>::Cons(d_a0, nullptr));
              *(_write) = std::move(_cell);
              _write = &std::get<typename List<unsigned int>::Cons>(
                            (*_write)->v_mut())
                            .d_a1;
              List<unsigned int> _next_l1 = *(d_a1);
              unsigned int _next_fuel = f;
              _loop_l1 = std::move(_next_l1);
              _loop_fuel = std::move(_next_fuel);
              continue;
            } else {
              auto _cell = std::make_unique<List<unsigned int>>(
                  typename List<unsigned int>::Cons(d_a00, nullptr));
              *(_write) = std::move(_cell);
              _write = &std::get<typename List<unsigned int>::Cons>(
                            (*_write)->v_mut())
                            .d_a1;
              List<unsigned int> _next_l2 = *(d_a10);
              unsigned int _next_fuel = f;
              _loop_l2 = std::move(_next_l2);
              _loop_fuel = std::move(_next_fuel);
              continue;
            }
          }
        }
      }
    }
    return std::move(*(_head));
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
