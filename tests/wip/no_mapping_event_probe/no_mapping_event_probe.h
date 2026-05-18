#ifndef INCLUDED_NO_MAPPING_EVENT_PROBE
#define INCLUDED_NO_MAPPING_EVENT_PROBE

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

struct NoMappingEventProbe {
  struct reproE {
    // TYPES
    struct Hidden {
      uint64_t a0;
      uint64_t a1;
    };

    struct Revealed {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<Hidden, Revealed>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    reproE() {}

    explicit reproE(Hidden _v) : v_(std::move(_v)) {}

    explicit reproE(Revealed _v) : v_(std::move(_v)) {}

    reproE(const reproE &_other) : v_(std::move(_other.clone().v_)) {}

    reproE(reproE &&_other) noexcept : v_(std::move(_other.v_)) {}

    reproE &operator=(const reproE &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    reproE &operator=(reproE &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    reproE clone() const {
      if (std::holds_alternative<Hidden>(this->v())) {
        const auto &[a0, a1] = std::get<Hidden>(this->v());
        return reproE(Hidden{a0, a1});
      } else {
        const auto &[a0, a1] = std::get<Revealed>(this->v());
        return reproE(Revealed{a0, a1});
      }
    }

    // CREATORS
    static reproE hidden(uint64_t a0, uint64_t a1) {
      return reproE(Hidden{a0, a1});
    }

    static reproE revealed(uint64_t a0, uint64_t a1) {
      return reproE(Revealed{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 reproE_rect(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[a0, a1] = std::get<typename reproE::Hidden>(r.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(a0, a1);
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &, uint64_t &>
  static T1 reproE_rec(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[a0, a1] = std::get<typename reproE::Hidden>(r.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(a0, a1);
    }
  }

  static inline const uint64_t cell_size = UINT64_C(42);
  static void draw_hidden_tile(uint64_t x, uint64_t y);
  static void draw_revealed_tile(uint64_t x, uint64_t y);
  static void loop(uint64_t x, uint64_t y, const List<bool> &cells);
};

#endif // INCLUDED_NO_MAPPING_EVENT_PROBE
