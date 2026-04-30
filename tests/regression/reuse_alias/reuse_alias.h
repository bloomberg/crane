#ifndef INCLUDED_REUSE_ALIAS
#define INCLUDED_REUSE_ALIAS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseAlias {
  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    mylist<t_A> clone() const {
      mylist<t_A> _out{};

      struct _CloneFrame {
        const mylist<t_A> *_src;
        mylist<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<t_A> *_src = _frame._src;
        mylist<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->d_v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{
              _alt.d_a0, _alt.d_a1 ? std::make_unique<mylist<t_A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        d_v_ = Mycons{t_A(d_a0),
                      d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    static mylist<t_A> mynil() { return mylist(Mynil{}); }

    static mylist<t_A> mycons(t_A a0, mylist<t_A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<t_A>>> _stack{};
      auto _drain = [&](mylist<t_A> &_node) {
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

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rect(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, mylist<T1>, T2> F1>
  static T2 mylist_rec(const T2 f, F1 &&f0, const mylist<T1> &m) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(m.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(m.v());
      return f0(d_a0, *(d_a1), mylist_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1> static unsigned int length(const mylist<T1> &l) {
    if (std::holds_alternative<typename mylist<T1>::Mynil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename mylist<T1>::Mycons>(l.v());
      return (length<T1>(*(d_a1)) + 1);
    }
  }

  /// Increment the head — candidate for reuse optimization when use_count = 1.
  static mylist<unsigned int> inc_head(const mylist<unsigned int> &l);
  /// Use the same list twice: once through inc_head, once directly.
  /// If reuse fires on the first call (because evaluation order is
  /// unspecified), the second use of l sees the already-mutated list.
  static std::pair<mylist<unsigned int>, mylist<unsigned int>>
  double_use(mylist<unsigned int> l);
  /// Pass the same list to two different functions.
  static std::pair<unsigned int, unsigned int>
  double_call(const mylist<unsigned int> &l);
  /// Alias through let-binding, then use both the alias and the original
  /// in a match.
  static std::pair<mylist<unsigned int>, unsigned int>
  alias_and_match(mylist<unsigned int> l);
  /// Build a result that refers to the scrutinee AND a pattern variable
  /// from the same match.
  static std::pair<mylist<unsigned int>, mylist<unsigned int>>
  scrutinee_in_branch(mylist<unsigned int> l);

  /// Chain inc_head: each call might try to reuse.
  static mylist<unsigned int> triple_inc(const mylist<unsigned int> &l);
};

#endif // INCLUDED_REUSE_ALIAS
