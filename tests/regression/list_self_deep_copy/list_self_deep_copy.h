#ifndef INCLUDED_LIST_SELF_DEEP_COPY
#define INCLUDED_LIST_SELF_DEEP_COPY

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
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

struct ListSelfDeepCopy {
  /// Recursive occurrence hidden under stdlib list.  The list spine has its
  /// own iterative clone, so the generated C++ compiles.  However, each list
  /// element copy re-enters chain::clone recursively; copying a deep
  /// single-child chain with dup_chain therefore overflows the C++ stack.
  struct chain {
    // TYPES
    struct Stop {};

    struct Link {
      std::unique_ptr<List<chain>> d_a0;
    };

    using variant_t = std::variant<Stop, Link>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : d_v_(_v) {}

    explicit chain(Link _v) : d_v_(std::move(_v)) {}

    chain(const chain &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    chain(chain &&_other) : d_v_(std::move(_other.d_v_)) {}

    chain &operator=(const chain &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    chain &operator=(chain &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    chain clone() const {
      chain _out{};

      struct _CloneFrame {
        const chain *_src;
        chain *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const chain *_src = _frame._src;
        chain *_dst = _frame._dst;
        if (std::holds_alternative<Stop>(_src->v())) {
          _dst->d_v_ = Stop{};
        } else {
          const auto &_alt = std::get<Link>(_src->v());
          _dst->d_v_ =
              Link{_alt.d_a0 ? std::make_unique<List<ListSelfDeepCopy::chain>>()
                             : nullptr};
          auto &_dst_alt = std::get<Link>(_dst->d_v_);
          [&] {
            if (_alt.d_a0) {
              const List<ListSelfDeepCopy::chain> *_lsrc = _alt.d_a0.get();
              List<ListSelfDeepCopy::chain> *_ldst = _dst_alt.d_a0.get();
              while (std::holds_alternative<
                     typename List<ListSelfDeepCopy::chain>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<ListSelfDeepCopy::chain>::Cons>(
                        _lsrc->v());
                _ldst->v_mut() = typename List<ListSelfDeepCopy::chain>::Cons{
                    ListSelfDeepCopy::chain{},
                    _lsrc_c.d_a1
                        ? std::make_unique<List<ListSelfDeepCopy::chain>>()
                        : nullptr};
                auto &_ldst_c =
                    std::get<typename List<ListSelfDeepCopy::chain>::Cons>(
                        _ldst->v_mut());
                _stack.push_back({&_lsrc_c.d_a0, &_ldst_c.d_a0});
                if (_lsrc_c.d_a1) {
                  _lsrc = _lsrc_c.d_a1.get();
                  _ldst = _ldst_c.d_a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<
                      typename List<ListSelfDeepCopy::chain>::Nil>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<ListSelfDeepCopy::chain>::Nil{};
              }
            }
          }();
        }
      }
      return _out;
    }

    // CREATORS
    static chain stop() { return chain(Stop{}); }

    static chain link(List<chain> a0) {
      return chain(Link{std::make_unique<List<chain>>(std::move(a0))});
    }

    // MANIPULATORS
    ~chain() {
      std::vector<std::unique_ptr<chain>> _stack{};
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Link>(_node.d_v_)) {
          auto &_alt = std::get<Link>(_node.d_v_);
          if (_alt.d_a0) {
            auto *_lp = _alt.d_a0.get();
            while (std::holds_alternative<
                   typename List<ListSelfDeepCopy::chain>::Cons>(_lp->v())) {
              auto &_lc =
                  std::get<typename List<ListSelfDeepCopy::chain>::Cons>(
                      _lp->v_mut());
              _stack.push_back(std::make_unique<ListSelfDeepCopy::chain>(
                  std::move(_lc.d_a0)));
              if (_lc.d_a1) {
                _lp = _lc.d_a1.get();
              } else {
                break;
              }
            }
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, List<chain> &>
  static T1 chain_rect(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::Link>(c.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, List<chain> &>
  static T1 chain_rec(const T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[d_a0] = std::get<typename chain::Link>(c.v());
      return f0(*(d_a0));
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_LIST_SELF_DEEP_COPY
