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

struct NoMappingEventProbe {
  struct reproE {
    // TYPES
    struct Hidden {
      unsigned int a0;
      unsigned int a1;
    };

    struct Revealed {
      unsigned int a0;
      unsigned int a1;
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

    reproE(reproE &&_other) : v_(std::move(_other.v_)) {}

    reproE &operator=(const reproE &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    reproE &operator=(reproE &&_other) {
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
    static reproE hidden(unsigned int a0, unsigned int a1) {
      return reproE(Hidden{a0, a1});
    }

    static reproE revealed(unsigned int a0, unsigned int a1) {
      return reproE(Revealed{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &>
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
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, unsigned int &, unsigned int &>
  static T1 reproE_rec(F0 &&f, F1 &&f0, const reproE &r) {
    if (std::holds_alternative<typename reproE::Hidden>(r.v())) {
      const auto &[a0, a1] = std::get<typename reproE::Hidden>(r.v());
      return f(a0, a1);
    } else {
      const auto &[a0, a1] = std::get<typename reproE::Revealed>(r.v());
      return f0(a0, a1);
    }
  }

  static inline const unsigned int cell_size = 42u;
  static void draw_hidden_tile(unsigned int x, unsigned int y);
  static void draw_revealed_tile(unsigned int x, unsigned int y);
  static void loop(unsigned int x, unsigned int y, const List<bool> &cells);
};

#endif // INCLUDED_NO_MAPPING_EVENT_PROBE
