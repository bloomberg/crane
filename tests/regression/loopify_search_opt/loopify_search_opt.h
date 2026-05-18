#ifndef INCLUDED_LOOPIFY_SEARCH_OPT
#define INCLUDED_LOOPIFY_SEARCH_OPT

#include <algorithm>
#include <memory>
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

  uint64_t length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
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
};

struct LoopifySearchOpt {
  static List<uint64_t> lis(const List<uint64_t> &l);
  static List<uint64_t> longest_run_fuel(uint64_t fuel, List<uint64_t> current,
                                         List<uint64_t> best,
                                         const List<uint64_t> &l);
  static List<uint64_t> longest_run(const List<uint64_t> &l);
  static uint64_t
  knapsack_fuel(uint64_t fuel, uint64_t capacity,
                const List<std::pair<uint64_t, uint64_t>> &items);
  static uint64_t knapsack(uint64_t capacity,
                           const List<std::pair<uint64_t, uint64_t>> &items);
  static bool subset_sum_fuel(uint64_t fuel, uint64_t target,
                              const List<uint64_t> &l);
  static bool subset_sum(uint64_t target, const List<uint64_t> &l);
  static std::pair<uint64_t, uint64_t> majority(const List<uint64_t> &l);
  static bool binary_search_fuel(uint64_t fuel, uint64_t target,
                                 const List<uint64_t> &l);
  static bool binary_search(uint64_t target, const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_SEARCH_OPT
