#include "itree_reified.h"

/// Pass-through: takes a reified itree and returns it unchanged.
std::shared_ptr<ITree<std::monostate>>
ITreeReified::run_tree(std::shared_ptr<ITree<std::monostate>> t) {
  return t;
}

/// Sequence two reified itrees.
std::shared_ptr<ITree<std::monostate>>
ITreeReified::sequence_trees(const std::shared_ptr<ITree<std::monostate>> &t1,
                             const std::shared_ptr<ITree<std::monostate>> &t2) {
  return itree_bind(t1, [=](std::monostate) mutable { return t2; });
}

/// Direct mode (no itree params) should be unchanged.
std::shared_ptr<ITree<std::monostate>> ITreeReified::test_direct() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<std::monostate>> {
        std::cout << "direct1"s << '\n';
        return ITree<std::monostate>::ret(std::monostate{});
      }(),
      [](std::monostate) {
        return itree_bind(
            []() -> std::shared_ptr<ITree<std::monostate>> {
              std::cout << "direct2"s << '\n';
              return ITree<std::monostate>::ret(std::monostate{});
            }(),
            [](std::monostate) {
              return ITree<std::monostate>::ret(std::monostate{});
            });
      });
}

/// A simple tree to instrument.
std::shared_ptr<ITree<std::monostate>> ITreeReified::greet() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<std::monostate>> {
        std::cout << "Hello!"s << '\n';
        return ITree<std::monostate>::ret(std::monostate{});
      }(),
      [](std::monostate) {
        return ITree<std::monostate>::ret(std::monostate{});
      });
}

/// Apply with_logging to greet, producing itree (ioE +' ioE) unit.
std::shared_ptr<ITree<std::monostate>> ITreeReified::test_logging() {
  return with_logging<void, std::monostate>(greet());
}

/// ---- Main (auto-wrapper) ----
std::shared_ptr<ITree<std::monostate>> ITreeReified::main() {
  return itree_bind(
      []() -> std::shared_ptr<ITree<std::monostate>> {
        std::cout << "=== Starting ==="s << '\n';
        return ITree<std::monostate>::ret(std::monostate{});
      }(),
      [](std::monostate) {
        return itree_bind(
            run_tree([]() -> std::shared_ptr<ITree<std::monostate>> {
              std::cout << "Hello from reified mode!"s << '\n';
              return ITree<std::monostate>::ret(std::monostate{});
            }()),
            [](std::monostate) {
              return itree_bind(
                  sequence_trees(
                      []() -> std::shared_ptr<ITree<std::monostate>> {
                        std::cout << "First"s << '\n';
                        return ITree<std::monostate>::ret(std::monostate{});
                      }(),
                      []() -> std::shared_ptr<ITree<std::monostate>> {
                        std::cout << "Second"s << '\n';
                        return ITree<std::monostate>::ret(std::monostate{});
                      }()),
                  [](std::monostate) {
                    return itree_bind(
                        []() -> std::shared_ptr<ITree<std::monostate>> {
                          std::cout << "=== Done ==="s << '\n';
                          return ITree<std::monostate>::ret(std::monostate{});
                        }(),
                        [](std::monostate) {
                          return ITree<std::monostate>::ret(std::monostate{});
                        });
                  });
            });
      });
}

int main() {
  ITreeReified::main()->run();
  return 0;
}
