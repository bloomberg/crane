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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
};

struct LoopifyListAccess {
  static unsigned int nth(unsigned int n, const List<unsigned int> &l);
  static unsigned int last(const List<unsigned int> &l);
  static unsigned int index_of_aux(unsigned int x, const List<unsigned int> &l,
                                   unsigned int idx);
  static unsigned int index_of(unsigned int x, const List<unsigned int> &l);
  static bool member(unsigned int x, const List<unsigned int> &l);
  static unsigned int
  lookup(unsigned int key,
         const List<std::pair<unsigned int, unsigned int>> &l);
  static List<unsigned int>
  lookup_all(unsigned int key,
             const List<std::pair<unsigned int, unsigned int>> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static unsigned int find(F0 &&p, const List<unsigned int> &l) {
    unsigned int _result;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = 0u;
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          _result = a0;
          break;
        } else {
          _loop_l = a1.get();
        }
      }
    }
    return _result;
  }

  static unsigned int count(unsigned int x, const List<unsigned int> &l);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static unsigned int count_matching(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(a0)) {
        return (1u + count_matching(p, *a1));
      } else {
        return count_matching(p, *a1);
      }
    }
  }

  static bool elem_at_eq(unsigned int idx, unsigned int val,
                         const List<unsigned int> &l);
  static unsigned int nth_default(unsigned int n, unsigned int default0,
                                  const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
