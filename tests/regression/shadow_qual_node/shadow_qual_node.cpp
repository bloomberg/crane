#include <shadow_qual_node.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) ShadowQualNode::Node::Shadow
ShadowQualNode::id(const ShadowQualNode::Node::Shadow x) {
  return x;
}
