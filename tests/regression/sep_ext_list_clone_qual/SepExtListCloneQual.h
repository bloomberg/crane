#ifndef INCLUDED_SEPEXTLISTCLONEQUAL
#define INCLUDED_SEPEXTLISTCLONEQUAL

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

#include "Datatypes.h"

namespace SepExtListCloneQual {

template <typename A> struct Forest {
  // TYPES
  struct Leaf {};

  struct Node {
    A a0;
    std::shared_ptr<typename Datatypes::template List<Forest<A>>> a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Leaf _v) : v_(_v) {}

  explicit Forest(Node _v) : v_(std::move(_v)) {}

  template <typename _U> explicit Forest(const Forest<_U> &_other) {
    if (std::holds_alternative<typename Forest<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[a0, a1] = std::get<typename Forest<_U>::Node>(_other.v());
      this->v_ = Node{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a0.type() == typeid(A))
                return std::any_cast<A>(a0);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
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
              return std::any_cast<A>(a0);
            } else
              return A(a0);
          }(),
          a1 ? std::make_shared<
                   Datatypes::List<SepExtListCloneQual::Forest<A>>>(*a1)
             : nullptr};
    }
  }

  static Forest<A> leaf() { return Forest(Leaf{}); }

  static Forest<A> node(A a0, typename Datatypes::template List<Forest<A>> a1) {
    return Forest(
        Node{std::move(a0),
             std::make_shared<typename Datatypes::template List<Forest<A>>>(
                 std::move(a1))});
  }

  // MANIPULATORS
  ~Forest() {
    std::vector<std::shared_ptr<Forest<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          auto *_lp = _alt->a1.get();
          while (
              std::holds_alternative<typename Datatypes::List<Forest<A>>::Cons>(
                  _lp->v())) {
            auto &_lc = std::get<typename Datatypes::List<Forest<A>>::Cons>(
                _lp->v_mut());
            _stack.push_back(std::make_shared<Forest<A>>(std::move(_lc.a)));
            if (_lc.l) {
              _lp = _lc.l.get();
            } else {
              break;
            }
          }
          _alt->a1.reset();
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
};

} // namespace SepExtListCloneQual

#endif // INCLUDED_SEPEXTLISTCLONEQUAL
