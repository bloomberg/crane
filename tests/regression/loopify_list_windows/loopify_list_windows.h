#ifndef INCLUDED_LOOPIFY_LIST_WINDOWS
#define INCLUDED_LOOPIFY_LIST_WINDOWS

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
  inline variant_t &v_mut() { return d_v_; }

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

struct LoopifyListWindows {
  __attribute__((pure)) static unsigned int len(const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  map_cons_helper(unsigned int x, const List<List<unsigned int>> &ll);
  __attribute__((pure)) static List<unsigned int> drop(const unsigned int &m,
                                                       List<unsigned int> xs);
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  span_eq(const unsigned int &first, List<unsigned int> lst);
  __attribute__((pure)) static List<unsigned int>
  differences(const List<unsigned int> &l);
  __attribute__((pure)) static List<std::pair<unsigned int, unsigned int>>
  sliding_pairs(const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  inits(const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  tails(List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  take(const unsigned int &n, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  windows_fuel(const unsigned int &fuel, const unsigned int &n,
               const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  windows(const unsigned int &n, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  chunks_fuel(const unsigned int &fuel, const unsigned int &n,
              const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  chunks(const unsigned int &n, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  group_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  group(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_WINDOWS
