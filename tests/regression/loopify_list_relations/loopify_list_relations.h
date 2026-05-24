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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
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
