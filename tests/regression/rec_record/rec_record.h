#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecRecord {
  template <typename t_A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      t_A d_a0;
      std::unique_ptr<rlist<t_A>> d_a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    rlist() {}

    explicit rlist(Rnil _v) : d_v_(_v) {}

    explicit rlist(Rcons _v) : d_v_(std::move(_v)) {}

    rlist(const rlist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    rlist(rlist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    rlist<t_A> &operator=(const rlist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    rlist<t_A> &operator=(rlist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) rlist<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Rnil>(_sv.v())) {
        return rlist<t_A>(Rnil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Rcons>(_sv.v());
        return rlist<t_A>(Rcons{
            d_a0, d_a1 ? std::make_unique<RecRecord::rlist<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit rlist(const rlist<_U> &_other) {
      if (std::holds_alternative<typename rlist<_U>::Rnil>(_other.v())) {
        d_v_ = Rnil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename rlist<_U>::Rcons>(_other.v());
        d_v_ = Rcons{t_A(d_a0),
                     d_a1 ? std::make_unique<rlist<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static rlist<t_A> rnil() { return rlist(Rnil{}); }

    __attribute__((pure)) static rlist<t_A> rcons(t_A a0, rlist<t_A> a1) {
      return rlist(
          Rcons{std::move(a0), std::make_unique<rlist<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rlist() {
      std::vector<std::unique_ptr<rlist>> _stack;
      auto _drain = [&](rlist &_node) {
        if (std::holds_alternative<Rcons>(_node.d_v_)) {
          auto &_alt = std::get<Rcons>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, rlist<T1>, T2> F1>
  static T2 rlist_rect(const T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(d_a0, *(d_a1), rlist_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1, rlist<T1>, T2> F1>
  static T2 rlist_rec(const T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(d_a0, *(d_a1), rlist_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  struct RNode {
    unsigned int rn_value;
    std::optional<std::unique_ptr<RNode>> rn_next;

    // ACCESSORS
    __attribute__((pure)) RNode clone() const {
      return RNode{(*(this)).rn_value,
                   (*this).rn_next.has_value()
                       ? std::make_optional(std::make_unique<RNode>(
                             (*(*this).rn_next)->clone()))
                       : std::nullopt};
    }
  };

  template <typename T1, MapsTo<T1, unsigned int, std::optional<RNode>> F0>
  static T1 RNode_rect(F0 &&f, const RNode &r) {
    unsigned int rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 =
        r.rn_next.has_value() ? std::make_optional<RNode>((*r.rn_next)->clone())
                              : std::nullopt;
    return f(rn_value0, rn_next0);
  }

  template <typename T1, MapsTo<T1, unsigned int, std::optional<RNode>> F0>
  static T1 RNode_rec(F0 &&f, const RNode &r) {
    unsigned int rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 =
        r.rn_next.has_value() ? std::make_optional<RNode>((*r.rn_next)->clone())
                              : std::nullopt;
    return f(rn_value0, rn_next0);
  }

  struct Employee {
    unsigned int emp_name;
    unsigned int emp_dept;

    // ACCESSORS
    __attribute__((pure)) Employee clone() const {
      return Employee{(*(this)).emp_name, (*(this)).emp_dept};
    }
  };

  struct Department {
    unsigned int dept_id;
    Employee dept_head;
    unsigned int dept_size;

    // ACCESSORS
    __attribute__((pure)) Department clone() const {
      return Department{(*(this)).dept_id, (*(this)).dept_head.clone(),
                        (*(this)).dept_size};
    }
  };

  template <typename T1>
  __attribute__((pure)) static unsigned int rlist_length(const rlist<T1> &l) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(l.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename rlist<T1>::Rcons>(l.v());
      return (rlist_length<T1>(*(d_a1)) + 1);
    }
  }

  __attribute__((pure)) static unsigned int
  rlist_sum(const rlist<unsigned int> &l);
  __attribute__((pure)) static unsigned int rnode_depth(const RNode &r);
  static inline const rlist<unsigned int> test_rlist =
      rlist<unsigned int>::rcons(
          1u,
          rlist<unsigned int>::rcons(
              2u, rlist<unsigned int>::rcons(3u, rlist<unsigned int>::rnil())));
  static inline const unsigned int test_rlist_len =
      rlist_length<unsigned int>(test_rlist);
  static inline const unsigned int test_rlist_sum = rlist_sum(test_rlist);
  static inline const RNode test_rnode = RNode{
      1u,
      [](auto &&__x)
          -> std::optional<std::unique_ptr<RNode>> {
        return __x.has_value()
                   ? std::make_optional(std::make_unique<RNode>((*__x).clone()))
                   : std::nullopt;
      }(std::make_optional<RNode>(RNode{
              2u,
              [](auto &&__x)
                  -> std::optional<std::unique_ptr<RNode>> {
                return __x.has_value()
                           ? std::make_optional(
                                 std::make_unique<RNode>((*__x).clone()))
                           : std::nullopt;
              }(std::make_optional<RNode>(RNode{
                      3u,
                      [](auto &&__x) -> std::optional<std::unique_ptr<RNode>> {
                        return __x.has_value()
                                   ? std::make_optional(std::make_unique<RNode>(
                                         (*__x).clone()))
                                   : std::nullopt;
                      }(std::optional<RNode>())}))}))};
  static inline const unsigned int test_rnode_depth = rnode_depth(test_rnode);
  static inline const Employee test_emp = Employee{42u, 7u};
  static inline const Department test_dept = Department{7u, test_emp, 50u};
  static inline const unsigned int test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
