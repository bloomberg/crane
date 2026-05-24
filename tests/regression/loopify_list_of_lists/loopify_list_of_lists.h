#ifndef INCLUDED_LOOPIFY_LIST_OF_LISTS
#define INCLUDED_LOOPIFY_LIST_OF_LISTS

#include <algorithm>
#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct LoopifyListOfLists {
  static List<uint64_t> intercalate(const List<uint64_t> &sep,
                                    const List<List<uint64_t>> &ll);
  static List<uint64_t> map_hd(const List<List<uint64_t>> &ll);
  static List<List<uint64_t>> map_tl(const List<List<uint64_t>> &ll);
  static bool all_empty(const List<List<uint64_t>> &ll);
  static List<List<uint64_t>> transpose_fuel(uint64_t fuel,
                                             const List<List<uint64_t>> &ll);
  static uint64_t list_len(const List<uint64_t> &l);
  static uint64_t total_length(const List<List<uint64_t>> &ll);
  static List<List<uint64_t>> transpose(const List<List<uint64_t>> &ll);
  static List<uint64_t> flatten(const List<List<uint64_t>> &ll);
  static uint64_t count_total(const List<List<uint64_t>> &ll);
  static List<uint64_t> firsts(const List<List<uint64_t>> &ll);
  static bool all_nil(const List<List<uint64_t>> &ll);
  static List<std::pair<List<uint64_t>, List<uint64_t>>>
  zip_lists(const List<List<uint64_t>> &ll1, const List<List<uint64_t>> &ll2);
  static uint64_t max_length(const List<List<uint64_t>> &ll);
};

#endif // INCLUDED_LOOPIFY_LIST_OF_LISTS
