#ifndef INCLUDED_SEPEXTLISTCLONEQUAL
#define INCLUDED_SEPEXTLISTCLONEQUAL

#include <any>
#include <memory>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

} // namespace SepExtListCloneQual

#endif // INCLUDED_SEPEXTLISTCLONEQUAL
