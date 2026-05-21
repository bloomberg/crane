#ifndef INCLUDED_LOOPIFY_STRINGS
#define INCLUDED_LOOPIFY_STRINGS

#include <memory>
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
};

struct LoopifyStrings {
  static List<uint64_t> append(const List<uint64_t> &l1, List<uint64_t> l2);
  static List<uint64_t> join_with(uint64_t sep, const List<uint64_t> &l);
  static List<uint64_t> repeat_string(const List<uint64_t> &s, uint64_t n);
  static List<uint64_t> repeat_with_sep(List<uint64_t> s,
                                        const List<uint64_t> &sep, uint64_t n);
  static List<uint64_t> string_chain_fuel(uint64_t fuel,
                                          const List<uint64_t> &s, uint64_t n,
                                          const List<uint64_t> &sep,
                                          const List<uint64_t> &end_marker);
  static List<uint64_t> string_chain(const List<uint64_t> &s, uint64_t n,
                                     const List<uint64_t> &sep,
                                     const List<uint64_t> &end_marker);
  static List<uint64_t> reverse(const List<uint64_t> &l);
  static bool list_eq(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_palindrome(const List<uint64_t> &l);
  static List<uint64_t> intersperse(uint64_t sep, const List<uint64_t> &l);
  static List<uint64_t> intercalate(const List<uint64_t> &sep,
                                    const List<List<uint64_t>> &ll);
  static List<uint64_t> replicate(uint64_t n, uint64_t x);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_aux(uint64_t current, uint64_t count, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_STRINGS
