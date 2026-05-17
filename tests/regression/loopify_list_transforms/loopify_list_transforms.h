#ifndef INCLUDED_LOOPIFY_LIST_TRANSFORMS
#define INCLUDED_LOOPIFY_LIST_TRANSFORMS

#include <memory>
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

struct LoopifyListTransforms {
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
  static List<uint64_t> prefix_sums(uint64_t acc, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  sliding_pairs_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  sliding_pairs(const List<uint64_t> &l);
  static uint64_t abs_diff(uint64_t x, uint64_t y);
  static List<uint64_t> differences_fuel(uint64_t fuel,
                                         const List<uint64_t> &l);
  static List<uint64_t> differences(const List<uint64_t> &l);
  static List<uint64_t> take(uint64_t n, const List<uint64_t> &l);
  static List<uint64_t> drop(uint64_t n, List<uint64_t> l);
  static List<List<uint64_t>> chunks_of_fuel(uint64_t fuel, uint64_t n,
                                             const List<uint64_t> &l);
  static List<List<uint64_t>> chunks_of(uint64_t n, const List<uint64_t> &l);
  static List<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         List<uint64_t> l);
  static List<uint64_t> rotate_left(uint64_t n, const List<uint64_t> &l);
  static List<uint64_t> uniq_sorted_fuel(uint64_t fuel,
                                         const List<uint64_t> &l);
  static List<uint64_t> uniq_sorted(const List<uint64_t> &l);
  static uint64_t step_sum(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_TRANSFORMS
