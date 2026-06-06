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
      uint64_t a0;
      std::shared_ptr<mylist> a1;
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

    static mylist mynil() { return mylist(MyNil{}); }

    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(MyCons{a0, std::make_shared<mylist>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MyCons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(T1 f, F1 &&f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::MyNil>(m.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename mylist::MyCons>(m.v());
      return f0(a0, *a1, mylist_rec<T1>(f, f0, *a1));
    }
  } /// Four levels of nested matching.

  static uint64_t deep4(const mylist &a, const mylist &b, const mylist &c,
                        const mylist &d);
  /// Match in a let, then match on the let result.
  static uint64_t let_match_chain(const mylist &xs, const mylist &ys);
  /// Matching where the same list is matched multiple times.
  static uint64_t multi_match_same(const mylist &xs);
  /// Nested match where inner match scrutinee is a field from outer match.
  static uint64_t nested_field_match(const mylist &xs);
};

#endif // INCLUDED_NAME_CLASH_NESTED_DEEP
