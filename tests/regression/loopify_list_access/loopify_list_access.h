#ifndef INCLUDED_LOOPIFY_LIST_ACCESS
#define INCLUDED_LOOPIFY_LIST_ACCESS

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
    std::unique_ptr<List<A>> l;
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
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
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
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
};

struct LoopifyListAccess {
  static uint64_t nth(uint64_t n, const List<uint64_t> &l);
  static uint64_t last(const List<uint64_t> &l);
  static uint64_t index_of_aux(uint64_t x, const List<uint64_t> &l,
                               uint64_t idx);
  static uint64_t index_of(uint64_t x, const List<uint64_t> &l);
  static bool member(uint64_t x, const List<uint64_t> &l);
  static uint64_t lookup(uint64_t key,
                         const List<std::pair<uint64_t, uint64_t>> &l);
  static List<uint64_t>
  lookup_all(uint64_t key, const List<std::pair<uint64_t, uint64_t>> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t find(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          return a0;
        } else {
          _loop_l = a1.get();
        }
      }
    }
  }

  static uint64_t count(uint64_t x, const List<uint64_t> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static uint64_t count_matching(F0 &&p, const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      if (p(a0)) {
        return (UINT64_C(1) + count_matching(p, *a1));
      } else {
        return count_matching(p, *a1);
      }
    }
  }

  static bool elem_at_eq(uint64_t idx, uint64_t val, const List<uint64_t> &l);
  static uint64_t nth_default(uint64_t n, uint64_t default0,
                              const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
