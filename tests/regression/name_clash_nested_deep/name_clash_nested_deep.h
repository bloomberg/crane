#ifndef INCLUDED_NAME_CLASH_NESTED_DEEP
#define INCLUDED_NAME_CLASH_NESTED_DEEP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct NameClashNestedDeep {
  /// Deep nesting of pattern matches to stress name generation.
  /// Each level creates d_a0, d_a00, d_a01, etc.
  struct mylist {
    // TYPES
    struct MyNil {};

    struct MyCons {
      unsigned int a0;
      std::unique_ptr<mylist> a1;
    };

    using variant_t = std::variant<MyNil, MyCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(MyNil _v) : v_(_v) {}

    explicit mylist(MyCons _v) : v_(std::move(_v)) {}

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist clone() const {
      mylist _out{};

      struct _CloneFrame {
        const mylist *_src;
        mylist *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<MyNil>(_src->v())) {
          _dst->v_ = MyNil{};
        } else {
          const auto &_alt = std::get<MyCons>(_src->v());
          _dst->v_ =
              MyCons{_alt.a0, _alt.a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<MyCons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mynil() { return mylist(MyNil{}); }

    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(MyCons{a0, std::make_unique<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<MyCons>(_node.v_)) {
          auto &_alt = std::get<MyCons>(_node.v_);
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &, mylist &, T1 &>
  static T1 mylist_rect(T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, unsigned int &, mylist &, T1 &>
  static T1 mylist_rec(T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(a0, *a1, mylist_rec<T1>(f, f0, *a1));
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
