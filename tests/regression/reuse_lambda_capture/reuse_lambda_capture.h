#ifndef INCLUDED_REUSE_LAMBDA_CAPTURE
#define INCLUDED_REUSE_LAMBDA_CAPTURE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ReuseLambdaCapture {
  /// Define mycons FIRST so it gets variant index 0.
  /// The reuse optimization picks List.hd reuse_candidates, i.e. the
  /// first constructor branch with a matching tail constructor.
  /// By putting mycons at index 0, reuse fires on the mycons branch.
  struct mylist {
    // TYPES
    struct Mycons {
      uint64_t a0;
      std::unique_ptr<mylist> a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : v_(_v) {}

    mylist(const mylist &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist &operator=(const mylist &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist &operator=(mylist &&_other) noexcept {
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
        if (std::holds_alternative<Mycons>(_src->v())) {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ =
              Mycons{_alt.a0, _alt.a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          _dst->v_ = Mynil{};
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mycons(uint64_t a0, mylist a1) {
      return mylist(Mycons{a0, std::make_unique<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rect(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rect<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, mylist &, T1 &>
  static T1 mylist_rec(F0 &&f, T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(m.v());
      return f(a0, *a1, mylist_rec<T1>(f, f0, *a1));
    } else {
      return f0;
    }
  }

  static uint64_t length(const mylist &l);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static mylist map(F0 &&f, const mylist &l) {
    if (std::holds_alternative<typename mylist::Mycons>(l.v())) {
      const auto &[a0, a1] = std::get<typename mylist::Mycons>(l.v());
      return mylist::mycons(f(a0), map(f, *a1));
    } else {
      return mylist::mynil();
    }
  }

  /// BUG: reuse fires, then length l inside the lambda accesses
  /// moved-from fields of l.
  ///
  /// The reuse path does:
  /// auto x  = std::move(_rf.d_a0);
  /// auto xs = std::move(_rf.d_a1);   // _rf.d_a1 is now null
  /// _rf.d_a0 = x + 1;
  /// _rf.d_a1 = map(lambda, xs);      // lambda calls length(l)
  /// // l is the same object as _rf
  /// // l.d_a1 is null -> crash
  /// return _rf;
  static mylist add_length_to_each(mylist l, bool b);
  static inline const uint64_t test1 = length(add_length_to_each(
      mylist::mycons(
          UINT64_C(10),
          mylist::mycons(UINT64_C(20),
                         mylist::mycons(UINT64_C(30), mylist::mynil()))),
      true));
  /// Expected: map adds length(original list)=3 to each tail element.
  /// Original: 10, 20, 30
  /// Result:   11, 23, 33  (h+1=11, 20+3=23, 30+3=33)
  /// Length = 3
  static inline const uint64_t test2 = []() {
    auto &&_sv0 = add_length_to_each(
        mylist::mycons(UINT64_C(5),
                       mylist::mycons(UINT64_C(6), mylist::mynil())),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0.v())) {
      const auto &[a00, a10] = std::get<typename mylist::Mycons>(_sv0.v());
      return a00;
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_REUSE_LAMBDA_CAPTURE
