#ifndef INCLUDED_CONCEPT_QUALIFY_ARGS
#define INCLUDED_CONCEPT_QUALIFY_ARGS

#include <concepts>
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
        _dst->d_v_ = Nil();
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons(_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr);
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
      this->d_v_ = Nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ =
          Cons(t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr);
    }
  }

  static List<t_A> nil() { return List(Nil()); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons(std::move(a0), std::make_unique<List<t_A>>(std::move(a1))));
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
concept HasElements = requires {
  typename M::t;
  requires(
      requires {
        { M::elements } -> std::convertible_to<List<typename M::t>>;
      } ||
      requires {
        { M::elements() } -> std::convertible_to<List<typename M::t>>;
      });
  { M::head_or(std::declval<typename M::t>()) } -> std::same_as<typename M::t>;
};

struct ConceptQualifyArgs {
  template <HasElements E> struct UseElements {
    constexpr static typename E::t first_or_default(const typename E::t _x0) {
      return E::head_or(_x0);
    }
  };

  struct NatElems {
    using t = unsigned int;
    static inline const List<unsigned int> elements = List<unsigned int>::cons(
        1u, List<unsigned int>::cons(
                2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())));
    static unsigned int head_or(const unsigned int d);
  };

  using UseNatElems = UseElements<NatElems>;
  static inline const unsigned int test = UseNatElems::first_or_default(0u);
};

#endif // INCLUDED_CONCEPT_QUALIFY_ARGS
