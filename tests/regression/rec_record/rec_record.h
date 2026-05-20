#ifndef INCLUDED_REC_RECORD
#define INCLUDED_REC_RECORD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct RecRecord {
  template <typename A> struct rlist {
    // TYPES
    struct Rnil {};

    struct Rcons {
      A a0;
      std::unique_ptr<rlist<A>> a1;
    };

    using variant_t = std::variant<Rnil, Rcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rlist() {}

    explicit rlist(Rnil _v) : v_(_v) {}

    explicit rlist(Rcons _v) : v_(std::move(_v)) {}

    rlist(const rlist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    rlist(rlist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    rlist<A> &operator=(const rlist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    rlist<A> &operator=(rlist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    rlist<A> clone() const {
      rlist<A> _out{};

      struct _CloneFrame {
        const rlist<A> *_src;
        rlist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const rlist<A> *_src = _frame._src;
        rlist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Rnil>(_src->v())) {
          _dst->v_ = Rnil{};
        } else {
          const auto &_alt = std::get<Rcons>(_src->v());
          _dst->v_ =
              Rcons{_alt.a0, _alt.a1 ? std::make_unique<rlist<A>>() : nullptr};
          auto &_dst_alt = std::get<Rcons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit rlist(const rlist<_U> &_other) {
      if (std::holds_alternative<typename rlist<_U>::Rnil>(_other.v())) {
        this->v_ = Rnil{};
      } else {
        const auto &[a0, a1] = std::get<typename rlist<_U>::Rcons>(_other.v());
        this->v_ = Rcons{A(a0), a1 ? std::make_unique<rlist<A>>(*a1) : nullptr};
      }
    }

    static rlist<A> rnil() { return rlist(Rnil{}); }

    static rlist<A> rcons(A a0, rlist<A> a1) {
      return rlist(
          Rcons{std::move(a0), std::make_unique<rlist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rlist() {
      std::vector<std::unique_ptr<rlist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](rlist<A> &_node) {
        if (std::holds_alternative<Rcons>(_node.v_)) {
          auto &_alt = std::get<Rcons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, rlist<T1> &, T2 &>
  static T2 rlist_rect(T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(a0, *a1, rlist_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, rlist<T1> &, T2 &>
  static T2 rlist_rec(T2 f, F1 &&f0, const rlist<T1> &r) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(r.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(r.v());
      return f0(a0, *a1, rlist_rec<T1, T2>(f, f0, *a1));
    }
  }

  struct RNode {
    uint64_t rn_value;
    std::optional<std::unique_ptr<RNode>> rn_next;

    // ACCESSORS
    RNode clone() const {
      return RNode{this->rn_value,
                   (*this).rn_next.has_value()
                       ? std::make_optional(std::make_unique<RNode>(
                             (*(*this).rn_next)->clone()))
                       : std::nullopt};
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<RNode> &>
  static T1 RNode_rect(F0 &&f, const RNode &r) {
    uint64_t rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 =
        r.rn_next.has_value() ? std::make_optional<RNode>((*r.rn_next)->clone())
                              : std::nullopt;
    return f(rn_value0, rn_next0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<RNode> &>
  static T1 RNode_rec(F0 &&f, const RNode &r) {
    uint64_t rn_value0 = r.rn_value;
    std::optional<RNode> rn_next0 =
        r.rn_next.has_value() ? std::make_optional<RNode>((*r.rn_next)->clone())
                              : std::nullopt;
    return f(rn_value0, rn_next0);
  }

  struct Employee {
    uint64_t emp_name;
    uint64_t emp_dept;

    // ACCESSORS
    Employee clone() const { return Employee{this->emp_name, this->emp_dept}; }
  };

  struct Department {
    uint64_t dept_id;
    Employee dept_head;
    uint64_t dept_size;

    // ACCESSORS
    Department clone() const {
      return Department{this->dept_id, this->dept_head.clone(),
                        this->dept_size};
    }
  };

  template <typename T1> static uint64_t rlist_length(const rlist<T1> &l) {
    if (std::holds_alternative<typename rlist<T1>::Rnil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename rlist<T1>::Rcons>(l.v());
      return (rlist_length<T1>(*a1) + 1);
    }
  }

  static uint64_t rlist_sum(const rlist<uint64_t> &l);
  static uint64_t rnode_depth(const RNode &r);
  static inline const rlist<uint64_t> test_rlist = rlist<uint64_t>::rcons(
      UINT64_C(1), rlist<uint64_t>::rcons(
                       UINT64_C(2), rlist<uint64_t>::rcons(
                                        UINT64_C(3), rlist<uint64_t>::rnil())));
  static inline const uint64_t test_rlist_len =
      rlist_length<uint64_t>(test_rlist);
  static inline const uint64_t test_rlist_sum = rlist_sum(test_rlist);
  static inline const RNode test_rnode = RNode{
      UINT64_C(1),
      [](auto &&__x)
          -> std::optional<std::unique_ptr<RNode>> {
        return __x.has_value()
                   ? std::make_optional(std::make_unique<RNode>((*__x).clone()))
                   : std::nullopt;
      }(std::make_optional<RNode>(RNode{
              UINT64_C(2),
              [](auto &&__x)
                  -> std::optional<std::unique_ptr<RNode>> {
                return __x.has_value()
                           ? std::make_optional(
                                 std::make_unique<RNode>((*__x).clone()))
                           : std::nullopt;
              }(std::make_optional<RNode>(RNode{
                      UINT64_C(3),
                      [](auto &&__x) -> std::optional<std::unique_ptr<RNode>> {
                        return __x.has_value()
                                   ? std::make_optional(std::make_unique<RNode>(
                                         (*__x).clone()))
                                   : std::nullopt;
                      }(std::optional<RNode>())}))}))};
  static inline const uint64_t test_rnode_depth = rnode_depth(test_rnode);
  static inline const Employee test_emp = Employee{UINT64_C(42), UINT64_C(7)};
  static inline const Department test_dept =
      Department{UINT64_C(7), test_emp, UINT64_C(50)};
  static inline const uint64_t test_dept_head_name =
      test_dept.dept_head.emp_name;
};

#endif // INCLUDED_REC_RECORD
