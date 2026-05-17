#ifndef INCLUDED_PATTERN_IMPOSSIBLE
#define INCLUDED_PATTERN_IMPOSSIBLE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct PatternImpossible {
  enum class Three { ONE, TWO, THREE };

  template <typename T1> static T1 three_rect(T1 f, T1 f0, T1 f1, Three t) {
    switch (t) {
    case Three::ONE: {
      return f;
    }
    case Three::TWO: {
      return f0;
    }
    case Three::THREE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 three_rec(T1 f, T1 f0, T1 f1, Three t) {
    switch (t) {
    case Three::ONE: {
      return f;
    }
    case Three::TWO: {
      return f0;
    }
    case Three::THREE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  struct nested {
    // TYPES
    struct Leaf {
      unsigned int a0;
    };

    struct Node {
      std::unique_ptr<nested> a0;
      std::unique_ptr<nested> a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nested() {}

    explicit nested(Leaf _v) : v_(std::move(_v)) {}

    explicit nested(Node _v) : v_(std::move(_v)) {}

    nested(const nested &_other) : v_(std::move(_other.clone().v_)) {}

    nested(nested &&_other) noexcept : v_(std::move(_other.v_)) {}

    nested &operator=(const nested &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    nested &operator=(nested &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    nested clone() const {
      nested _out{};

      struct _CloneFrame {
        const nested *_src;
        nested *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const nested *_src = _frame._src;
        nested *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          const auto &_alt = std::get<Leaf>(_src->v());
          _dst->v_ = Leaf{_alt.a0};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<nested>() : nullptr,
                          _alt.a1 ? std::make_unique<nested>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static nested leaf(unsigned int a0) { return nested(Leaf{a0}); }

    static nested node(nested a0, nested a1) {
      return nested(Node{std::make_unique<nested>(std::move(a0)),
                         std::make_unique<nested>(std::move(a1))});
    }

    // MANIPULATORS
    ~nested() {
      std::vector<std::unique_ptr<nested>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](nested &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
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

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, nested &, T1 &, nested &, T1 &>
  static T1 nested_rect(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[a0] = std::get<typename nested::Leaf>(n.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename nested::Node>(n.v());
      return f0(*a0, nested_rect<T1>(f, f0, *a0), *a1,
                nested_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F1 &, nested &, T1 &, nested &, T1 &>
  static T1 nested_rec(F0 &&f, F1 &&f0, const nested &n) {
    if (std::holds_alternative<typename nested::Leaf>(n.v())) {
      const auto &[a0] = std::get<typename nested::Leaf>(n.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename nested::Node>(n.v());
      return f0(*a0, nested_rec<T1>(f, f0, *a0), *a1,
                nested_rec<T1>(f, f0, *a1));
    }
  }

  static unsigned int complex_match(Three x);
  static unsigned int nested_match(const nested &n);
  static unsigned int double_match(Three x, Three y);
  static unsigned int multi_arg_pattern(const nested &n);
  static inline const unsigned int test1 = complex_match(Three::ONE);
  static inline const unsigned int test2 =
      nested_match(nested::node(nested::leaf(5u), nested::leaf(10u)));
  static inline const unsigned int test3 = double_match(Three::ONE, Three::TWO);
};

#endif // INCLUDED_PATTERN_IMPOSSIBLE
