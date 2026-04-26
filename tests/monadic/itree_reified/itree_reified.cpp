#include <itree_reified.h>

#include <any>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// Pass-through: takes a reified itree and returns it unchanged.
void ITreeReified::run_tree(std::shared_ptr<ITree<void>>) { return; }

/// Sequence two reified itrees.
void ITreeReified::sequence_trees(const std::shared_ptr<ITree<void>> &t1,
                                  std::shared_ptr<ITree<void>> t2) {
  {
    itree_bind(t1, [=]() mutable { return t2; });
    return;
  }
}

/// Direct mode (no itree params) should be unchanged.
std::shared_ptr<ITree<void>> ITreeReified::test_direct() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<void>> {
        std::cout << "direct1"s << '\n';
        return ITree<void>::ret();
      }(),
      []() {
        return itree_bind(
            []() -> std::shared_ptr<ITree<void>> {
              std::cout << "direct2"s << '\n';
              return ITree<void>::ret();
            }(),
            []() { return ITree<void>::ret(); });
      });
}

/// A simple tree to instrument.
std::shared_ptr<ITree<void>> ITreeReified::greet() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<void>> {
        std::cout << "Hello!"s << '\n';
        return ITree<void>::ret();
      }(),
      []() { return ITree<void>::ret(); });
}

/// Apply with_logging to greet, producing itree (ioE +' ioE) unit.
std::shared_ptr<ITree<void>> ITreeReified::test_logging() {
  return with_logging([]() -> std::shared_ptr<ITree<void>> {
    greet();
    return ITree<void>::ret();
  }());
}

/// ---- Main (auto-wrapper) ----
std::shared_ptr<ITree<void>> ITreeReified::main() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<void>> {
        std::cout << "=== Starting ==="s << '\n';
        return ITree<void>::ret();
      }(),
      []() {
        return itree_bind(
            []() -> std::shared_ptr<ITree<void>> {
              run_tree([]() -> std::shared_ptr<ITree<void>> {
                std::cout << "Hello from reified mode!"s << '\n';
                return ITree<void>::ret();
              }());
              return ITree<void>::ret();
            }(),
            []() {
              return itree_bind(
                  []() -> std::shared_ptr<ITree<void>> {
                    sequence_trees(
                        []() -> std::shared_ptr<ITree<void>> {
                          std::cout << "First"s << '\n';
                          return ITree<void>::ret();
                        }(),
                        []() -> std::shared_ptr<ITree<void>> {
                          std::cout << "Second"s << '\n';
                          return ITree<void>::ret();
                        }());
                    return ITree<void>::ret();
                  }(),
                  []() {
                    return itree_bind(
                        []() -> std::shared_ptr<ITree<void>> {
                          std::cout << "=== Done ==="s << '\n';
                          return ITree<void>::ret();
                        }(),
                        []() { return ITree<void>::ret(); });
                  });
            });
      });
}

int main() {
  ITreeReified::main()->run();
  return 0;
}
