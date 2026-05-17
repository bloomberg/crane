#ifndef INCLUDED_LIST_SELF_DEEP_COPY
#define INCLUDED_LIST_SELF_DEEP_COPY

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

struct ListSelfDeepCopy {
  /// Recursive occurrence hidden under stdlib list.  The list spine has its
  /// own iterative clone, so the generated C++ compiles.  However, each list
  /// element copy re-enters chain::clone recursively; copying a deep
  /// single-child chain with dup_chain therefore overflows the C++ stack.
  struct chain {
    // TYPES
    struct Stop {};

    struct Link {
      std::unique_ptr<List<chain>> a0;
    };

    using variant_t = std::variant<Stop, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : v_(_v) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    chain(const chain &_other) : v_(std::move(_other.clone().v_)) {}

    chain(chain &&_other) : v_(std::move(_other.v_)) {}

    chain &operator=(const chain &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    chain &operator=(chain &&_other) {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const chain *_src = _frame._src;
        chain *_dst = _frame._dst;
        if (std::holds_alternative<Stop>(_src->v())) {
          _dst->v_ = Stop{};
        } else {
          const auto &_alt = std::get<Link>(_src->v());
          _dst->v_ = Link{_alt.a0 ? std::make_unique<List<chain>>() : nullptr};
          auto &_dst_alt = std::get<Link>(_dst->v_);
          [&] {
            if (_alt.a0) {
              const List<chain> *_lsrc = _alt.a0.get();
              List<chain> *_ldst = _dst_alt.a0.get();
              while (std::holds_alternative<typename List<chain>::Cons>(
                  _lsrc->v())) {
                const auto &_lsrc_c =
                    std::get<typename List<chain>::Cons>(_lsrc->v());
                _ldst->v_mut() = typename List<chain>::Cons{
                    chain{},
                    _lsrc_c.a1 ? std::make_unique<List<chain>>() : nullptr};
                auto &_ldst_c =
                    std::get<typename List<chain>::Cons>(_ldst->v_mut());
                _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
                if (_lsrc_c.a1) {
                  _lsrc = _lsrc_c.a1.get();
                  _ldst = _ldst_c.a1.get();
                } else {
                  break;
                }
              }
              if (std::holds_alternative<typename List<chain>::Nil>(
                      _lsrc->v())) {
                _ldst->v_mut() = typename List<chain>::Nil{};
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
      _stack.reserve(8);
      auto _drain = [&](chain &_node) {
        if (std::holds_alternative<Link>(_node.v_)) {
          auto &_alt = std::get<Link>(_node.v_);
          if (_alt.a0) {
            auto *_lp = _alt.a0.get();
            while (
                std::holds_alternative<typename List<chain>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<chain>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<chain>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, List<chain> &>
  static T1 chain_rect(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, List<chain> &>
  static T1 chain_rec(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_LIST_SELF_DEEP_COPY
