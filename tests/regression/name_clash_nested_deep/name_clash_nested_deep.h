#ifndef INCLUDED_NAME_CLASH_NESTED_DEEP
#define INCLUDED_NAME_CLASH_NESTED_DEEP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NameClashNestedDeep {
  /// Deep nesting of pattern matches to stress name generation.
  /// Each level creates d_a0, d_a00, d_a01, etc.
  struct mylist {
    // TYPES
    struct MyNil {};

    struct MyCons {
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    using variant_t = std::variant<MyNil, MyCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(MyNil _v) : d_v_(_v) {}

    explicit mylist(MyCons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist &operator=(const mylist &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<MyNil>(_src->v())) {
          const auto &_alt = std::get<MyNil>(_src->v());
          _dst->d_v_ = MyNil{};
        } else {
          const auto &_alt = std::get<MyCons>(_src->v());
          _dst->d_v_ = MyCons{_alt.d_a0,
                              _alt.d_a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<MyCons>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(MyNil{}); }

    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(
          MyCons{std::move(a0), std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack;
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<MyCons>(_node.d_v_)) {
          auto &_alt = std::get<MyCons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rect(const T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F1>
  static T1 mylist_rec(const T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rec<T1>(f, f0, *(d_a1)));
    }
  }

  /// Four levels of nested matching.
  static unsigned int deep4(const mylist &a, const mylist &b, const mylist &c,
                            const mylist &d);
  /// Match in a let, then match on the let result.
  static unsigned int let_match_chain(const mylist &xs, const mylist &ys);
  /// Matching where the same list is matched multiple times.
  static unsigned int multi_match_same(const mylist &xs);
  /// Nested match where inner match scrutinee is a field from outer match.
  static unsigned int nested_field_match(const mylist &xs);
};

#endif // INCLUDED_NAME_CLASH_NESTED_DEEP
