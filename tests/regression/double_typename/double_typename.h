#ifndef INCLUDED_DOUBLE_TYPENAME
#define INCLUDED_DOUBLE_TYPENAME

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
    _stack.reserve(8);
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
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ =
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
    _stack.reserve(8);
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

template <typename M>
concept OrderedType = requires { typename M::t; };

struct DoubleTypename {
  template <OrderedType X> struct MakeMap {
    template <typename t_A> struct entry {
      // TYPES
      struct Entry0 {
        typename X::t d_a0;
        t_A d_a1;
      };

      using variant_t = std::variant<Entry0>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      entry() {}

      explicit entry(Entry0 _v) : d_v_(std::move(_v)) {}

      entry(const entry<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

      entry(entry<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

      entry<t_A> &operator=(const entry<t_A> &_other) {
        d_v_ = std::move(_other.clone().d_v_);
        return *this;
      }

      entry<t_A> &operator=(entry<t_A> &&_other) {
        d_v_ = std::move(_other.d_v_);
        return *this;
      }

      // ACCESSORS
      entry<t_A> clone() const {
        auto &&_sv = *(this);
        const auto &[d_a0, d_a1] = std::get<Entry0>(_sv.v());
        return entry<t_A>(Entry0{d_a0, d_a1});
      }

      // CREATORS
      template <typename _U> explicit entry(const entry<_U> &_other) {
        const auto &[d_a0, d_a1] =
            std::get<typename entry<_U>::Entry0>(_other.v());
        this->d_v_ = Entry0{d_a0, t_A(d_a1)};
      }

      static entry<t_A> entry0(typename X::t a0, t_A a1) {
        return entry(Entry0{std::move(a0), std::move(a1)});
      }

      // MANIPULATORS
      inline variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      const variant_t &v() const { return d_v_; }
    };

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rect(F0 &&f, const entry<T1> &e) {
      const auto &[d_a0, d_a1] = std::get<typename entry<T1>::Entry0>(e.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, typename X::t &, T1 &>
    static T2 entry_rec(F0 &&f, const entry<T1> &e) {
      const auto &[d_a0, d_a1] = std::get<typename entry<T1>::Entry0>(e.v());
      return f(d_a0, d_a1);
    }

    template <typename T1>
    static List<typename X::t> keys(const List<entry<T1>> &l) {
      if (std::holds_alternative<typename List<entry<T1>>::Nil>(l.v())) {
        return List<typename X::t>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<entry<T1>>::Cons>(l.v());
        const auto &[d_a00, d_a10] =
            std::get<typename entry<T1>::Entry0>(d_a0.v());
        return List<typename X::t>::cons(d_a00, List<typename X::t>::nil());
      }
    }
  };

  struct NatOrd {
    using t = unsigned int;
  };

  using NatMap = MakeMap<NatOrd>;
  static inline const List<unsigned int> test =
      NatMap::template keys<unsigned int>(
          List<NatMap::entry<unsigned int>>::cons(
              NatMap::template entry<unsigned int>::entry0(1u, 2u),
              List<NatMap::entry<unsigned int>>::nil()));
};

#endif // INCLUDED_DOUBLE_TYPENAME
