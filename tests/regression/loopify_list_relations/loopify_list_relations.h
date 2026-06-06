#ifndef INCLUDED_LOOPIFY_LIST_RELATIONS
#define INCLUDED_LOOPIFY_LIST_RELATIONS

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct LoopifyListRelations {
  static bool is_prefix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_suffix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static bool is_infix_of_aux(const List<uint64_t> &needle,
                              const List<uint64_t> &haystack);
  static bool is_infix_of(const List<uint64_t> &_x0, const List<uint64_t> &_x1);
  static List<uint64_t> find_sublists_aux(const List<uint64_t> &needle,
                                          const List<uint64_t> &haystack,
                                          uint64_t idx);
  static List<uint64_t> find_sublists(const List<uint64_t> &needle,
                                      const List<uint64_t> &haystack);
  static bool list_eq(const List<uint64_t> &l1, const List<uint64_t> &l2);
  static uint64_t list_compare(const List<uint64_t> &l1,
                               const List<uint64_t> &l2);
  static List<std::pair<uint64_t, uint64_t>> zip(const List<uint64_t> &l1,
                                                 const List<uint64_t> &l2);
  static List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
  zip3(const List<uint64_t> &l1, const List<uint64_t> &l2,
       const List<uint64_t> &l3);
  static List<uint64_t> interleave(List<uint64_t> l1, List<uint64_t> l2);
  static List<uint64_t> merge_fuel(uint64_t fuel, List<uint64_t> l1,
                                   List<uint64_t> l2);
  static List<uint64_t> merge(const List<uint64_t> &l1,
                              const List<uint64_t> &l2);
  static List<uint64_t> union_(const List<uint64_t> &l1, List<uint64_t> l2);
  static List<uint64_t> intersection(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2);
};

#endif // INCLUDED_LOOPIFY_LIST_RELATIONS
