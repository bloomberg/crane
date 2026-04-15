#ifndef INCLUDED_LOOPIFY_LIST_OF_LISTS
#define INCLUDED_LOOPIFY_LIST_OF_LISTS

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<t_A>::Nil>(_loop_self->v())) {
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
        } else {
          _head = m;
        }
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(_loop_self->v());
        auto _cell = List<t_A>::cons(d_a0, nullptr);
        if (_last) {
          std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return _head;
  }
};

struct LoopifyListOfLists {
  static std::shared_ptr<List<unsigned int>> intercalate(
      const std::shared_ptr<List<unsigned int>> &sep,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<unsigned int>>
  map_hd(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  map_tl(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  __attribute__((pure)) static bool all_empty(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  transpose_fuel(
      const unsigned int fuel,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  __attribute__((pure)) static unsigned int
  list_len(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int total_length(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> transpose(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<unsigned int>>
  flatten(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  __attribute__((pure)) static unsigned int count_total(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<unsigned int>>
  firsts(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  __attribute__((pure)) static bool
  all_nil(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                                        std::shared_ptr<List<unsigned int>>>>>
  zip_lists(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll1,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll2);
  __attribute__((pure)) static unsigned int max_length(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
};

#endif // INCLUDED_LOOPIFY_LIST_OF_LISTS
