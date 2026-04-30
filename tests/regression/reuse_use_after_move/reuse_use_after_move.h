#ifndef INCLUDED_REUSE_USE_AFTER_MOVE
#define INCLUDED_REUSE_USE_AFTER_MOVE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseUseAfterMove {
  /// Define mycons FIRST so it gets variant index 0.
  /// This is critical: the reuse optimization picks List.hd reuse_candidates,
  /// i.e. the first constructor branch with a matching tail constructor.
  /// By putting mycons at index 0, the reuse optimization fires on the
  /// mycons branch instead of skipping to the no-op mynil branch.
  struct mylist {
    // TYPES
    struct Mycons {
      unsigned int d_a0;
      std::unique_ptr<mylist> d_a1;
    };

    struct Mynil {};

    using variant_t = std::variant<Mycons, Mynil>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

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

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist *_src = _frame._src;
        mylist *_dst = _frame._dst;
        if (std::holds_alternative<Mycons>(_src->v())) {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{_alt.d_a0,
                              _alt.d_a1 ? std::make_unique<mylist>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          _dst->d_v_ = Mynil{};
        }
      }
      return _out;
    }

    // CREATORS
    static mylist mycons(unsigned int a0, mylist a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist>(std::move(a1))});
    }

    static mylist mynil() { return mylist(Mynil{}); }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist>> _stack{};
      auto _drain = [&](mylist &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rect(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rect<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, mylist, T1> F0>
  static T1 mylist_rec(F0 &&f, const T1 f0, const mylist &m) {
    if (std::holds_alternative<typename mylist::Mycons>(m.v())) {
      const auto &[d_a0, d_a1] = std::get<typename mylist::Mycons>(m.v());
      return f(d_a0, *(d_a1), mylist_rec<T1>(f, f0, *(d_a1)));
    } else {
      return f0;
    }
  }

  static unsigned int length(const mylist &l);
  static unsigned int sum(const mylist &l);
  /// BUG: The reuse optimization fires because:
  /// 1. l escapes in the else branch (returned in tail position)
  /// -> infer_owned_params marks l as owned (pass by value)
  /// 2. The mycons branch has tail constructor mycons with arity 2 = 2
  /// -> find_reuse_candidates finds it as a candidate
  /// 3. mycons is at index 0 -> List.hd picks it
  /// 4. At runtime, use_count() == 1 holds for fresh values
  ///
  /// The reuse branch does:
  /// auto x  = std::move(_rf.d_a0);   // unsigned int, trivial
  /// auto xs = std::move(_rf.d_a1);   // shared_ptr -> NULL
  /// _rf.d_a0 = length(l);            // length accesses l.d_a1 which is NULL!
  /// _rf.d_a1 = xs;                   // restore xs
  /// return l;
  ///
  /// length(l) traverses l, hitting the null d_a1 field.
  /// Dereferencing null shared_ptr -> CRASH.
  static mylist rewrite_head(mylist l, const bool &b);
  /// test1: rewrite_head on 1, 2, 3 with true.
  /// Expected: length 1,2,3 = 3, so result = 3, 2, 3.
  /// Bug: null dereference inside length.
  static inline const unsigned int test1 = []() {
    auto &&_sv0 = rewrite_head(
        mylist::mycons(1u,
                       mylist::mycons(2u, mylist::mycons(3u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0.v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0.v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
  /// test2: Use sum instead of length — same bug pattern.
  static mylist rewrite_head_sum(mylist l, const bool &b);
  static inline const unsigned int test2 = []() {
    auto &&_sv0 = rewrite_head_sum(
        mylist::mycons(
            10u, mylist::mycons(20u, mylist::mycons(30u, mylist::mynil()))),
        true);
    if (std::holds_alternative<typename mylist::Mycons>(_sv0.v())) {
      const auto &[d_a00, d_a10] = std::get<typename mylist::Mycons>(_sv0.v());
      return d_a00;
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_REUSE_USE_AFTER_MOVE
