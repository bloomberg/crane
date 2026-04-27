#ifndef INCLUDED_LOOPIFY_LIST_ACCESS
#define INCLUDED_LOOPIFY_LIST_ACCESS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyListAccess {
  __attribute__((pure)) static unsigned int nth(const unsigned int &n,
                                                const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int last(const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  index_of_aux(const unsigned int &x, const List<unsigned int> &l,
               unsigned int idx);
  __attribute__((pure)) static unsigned int
  index_of(const unsigned int &x, const List<unsigned int> &l);
  __attribute__((pure)) static bool member(const unsigned int &x,
                                           const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int &key,
         const List<std::pair<unsigned int, unsigned int>> &l);
  __attribute__((pure)) static List<unsigned int>
  lookup_all(const unsigned int &key,
             const List<std::pair<unsigned int, unsigned int>> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int find(F0 &&p,
                                                 const List<unsigned int> &l) {
    unsigned int _result;
    List<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l.v())) {
        _result = 0u;
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          _result = d_a0;
          break;
        } else {
          _loop_l = *(d_a1);
        }
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int count(const unsigned int &x,
                                                  const List<unsigned int> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  count_matching(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return (1u + count_matching(p, *(d_a1)));
      } else {
        return count_matching(p, *(d_a1));
      }
    }
  }

  __attribute__((pure)) static bool elem_at_eq(const unsigned int &idx,
                                               const unsigned int &val,
                                               const List<unsigned int> &l);
  __attribute__((pure)) static unsigned int
  nth_default(const unsigned int &n, unsigned int default0,
              const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
