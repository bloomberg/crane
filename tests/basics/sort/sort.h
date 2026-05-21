#ifndef INCLUDED_SORT
#define INCLUDED_SORT

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct Compare_dec {
  static bool le_gt_dec(uint64_t _x0, uint64_t _x1);
  static bool le_dec(uint64_t n, uint64_t m);
};

struct Sort {
  template <typename T1, typename T2, typename F0, typename F2, typename F3>
    requires std::is_invocable_r_v<std::pair<List<T1>, List<T1>>, F0 &,
                                   List<T1> &> &&
             std::is_invocable_r_v<T2, F2 &, T1 &> &&
             std::is_invocable_r_v<T2, F3 &, List<T1> &, T2 &, T2 &>
  static T2 div_conq(F0 &&splitF, T2 x, F2 &&x0, F3 &&x1, const List<T1> &ls) {
    bool s = UINT64_C(2) <= ls.length();
    if (s) {
      return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
                div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
    } else {
      if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
        return x;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(ls.v());
        return x0(a0);
      }
    }
  }

  template <typename T1>
  static std::pair<List<T1>, List<T1>> split(const List<T1> &ls) {
    if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(ls.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return std::make_pair(List<T1>::cons(a0, List<T1>::nil()),
                              List<T1>::nil());
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(_sv0.v());
        auto _cs = split<T1>(*a10);
        const List<T1> &ls1 = _cs.first;
        const List<T1> &ls2 = _cs.second;
        return std::make_pair(List<T1>::cons(a0, ls1),
                              List<T1>::cons(a00, ls2));
      }
    }
  }

  template <typename T1, typename T2, typename F1, typename F2>
    requires std::is_invocable_r_v<T2, F1 &, T1 &> &&
             std::is_invocable_r_v<T2, F2 &, List<T1> &, T2 &, T2 &>
  static T2 div_conq_split(const T2 &x, F1 &&_x0, F2 &&_x1, List<T1> _x2) {
    return div_conq<T1, T2>(split<T1>, x, _x0, _x1, std::move(_x2));
  }

  template <typename T1, typename T2, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T2, F1 &, T1 &> &&
             std::is_invocable_r_v<T2, F2 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T2, F3 &, T1 &, T1 &, List<T1> &, T2 &, T2 &>
  static T2 div_conq_pair(T2 x, F1 &&x0, F2 &&x1, F3 &&x2, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return x0(a0);
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(_sv0.v());
        return x2(a0, a00, *a10, x1(a0, a00),
                  div_conq_pair<T1, T2>(x, x0, x1, x2, *a10));
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::pair<List<T1>, List<T1>>
  split_pivot(F0 &&le_dec0, const T1 &pivot, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto _cs = split_pivot<T1>(le_dec0, pivot, *a1);
      const List<T1> &l1 = _cs.first;
      const List<T1> &l2 = _cs.second;
      if (le_dec0(a0, pivot)) {
        return std::make_pair(List<T1>::cons(a0, l1), l2);
      } else {
        return std::make_pair(l1, List<T1>::cons(a0, l2));
      }
    }
  }

  template <typename T1, typename T2, typename F0, typename F2>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T2, F2 &, T1 &, List<T1> &, T2 &, T2 &>
  static T2 div_conq_pivot(F0 &&le_dec0, T2 x, F2 &&x0, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return x0(a0, *a1,
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot(le_dec0, a0, *a1).first),
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot(le_dec0, a0, *a1).second));
    }
  }

  static Sig<List<uint64_t>> sort_cons_prog(uint64_t a,
                                            const List<uint64_t> &_x,
                                            const List<uint64_t> &l_);
  static Sig<List<uint64_t>> isort(const List<uint64_t> &l);
  static List<uint64_t> merge(List<uint64_t> l1, const List<uint64_t> &l2);
  static Sig<List<uint64_t>> merge_prog(const List<uint64_t> &_x,
                                        const List<uint64_t> &l1,
                                        const List<uint64_t> &l2);
  static Sig<List<uint64_t>> msort(const List<uint64_t> &_x0);
  static Sig<List<uint64_t>> pair_merge_prog(uint64_t _x, uint64_t _x0,
                                             const List<uint64_t> &_x1,
                                             const List<uint64_t> &l_,
                                             const List<uint64_t> &l_0);
  static Sig<List<uint64_t>> psort(const List<uint64_t> &_x0);
  static Sig<List<uint64_t>> qsort(const List<uint64_t> &_x0);
};

#endif // INCLUDED_SORT
