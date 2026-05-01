# Copyright 2026 Bloomberg Finance L.P.
# Distributed under the terms of the GNU LGPL v2.1 license.
#
# Build for the Crane spreadsheet demo: a Rocq-extracted spreadsheet kernel
# driven by a Dear ImGui front-end.
#
# Expects the Crane theory to have been built first (so that the generated
# C++ sources for [Crane.Examples.Spreadsheet] exist under
# <project_root>/_build/default/Spreadsheet/).  Run `dune build theories`
# from the project root before invoking CMake.

cmake_minimum_required(VERSION 3.20)
project(crane-spreadsheet CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Locate the project root (two levels up from bin/spreadsheet/).
get_filename_component(CRANE_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
set(CRANE_THEORIES_CPP "${CRANE_ROOT}/theories/cpp")
# CRANE_GENERATED is the directory containing the Crane-extracted
# Spreadsheet.h / Spreadsheet.cpp.  Set on the cmake command line by the
# build helper, which runs rocq directly to produce them at a stable path.
if(NOT DEFINED CRANE_GENERATED)
  set(CRANE_GENERATED "${CRANE_ROOT}/_build/spreadsheet_gen")
endif()

if(NOT EXISTS "${CRANE_GENERATED}/Spreadsheet.cpp")
  message(FATAL_ERROR
    "Generated Spreadsheet.cpp not found at ${CRANE_GENERATED}.\n"
    "Build the kernel first: from the project root run\n"
    "  ./bin/spreadsheet/extract.sh  (or invoke rocq compile manually)")
endif()

# --- Dependencies -----------------------------------------------------------

find_package(OpenGL REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(GLFW REQUIRED IMPORTED_TARGET glfw3)

# Fetch Dear ImGui at configure time so reviewers don't need a submodule.
include(FetchContent)
FetchContent_Declare(
  imgui
  GIT_REPOSITORY https://github.com/ocornut/imgui.git
  GIT_TAG        v1.91.5
  GIT_SHALLOW    TRUE)
FetchContent_MakeAvailable(imgui)

# Build ImGui as a small static library: core + GLFW backend + OpenGL3 backend.
add_library(imgui STATIC
  ${imgui_SOURCE_DIR}/imgui.cpp
  ${imgui_SOURCE_DIR}/imgui_demo.cpp
  ${imgui_SOURCE_DIR}/imgui_draw.cpp
  ${imgui_SOURCE_DIR}/imgui_tables.cpp
  ${imgui_SOURCE_DIR}/imgui_widgets.cpp
  ${imgui_SOURCE_DIR}/backends/imgui_impl_glfw.cpp
  ${imgui_SOURCE_DIR}/backends/imgui_impl_opengl3.cpp)
target_include_directories(imgui PUBLIC
  ${imgui_SOURCE_DIR}
  ${imgui_SOURCE_DIR}/backends)
target_link_libraries(imgui PUBLIC PkgConfig::GLFW OpenGL::GL)

# --- The spreadsheet binary -------------------------------------------------

add_executable(spreadsheet
  main.cpp
  formula.cpp
  ${CRANE_GENERATED}/Spreadsheet.cpp)
target_include_directories(spreadsheet PRIVATE
  ${CRANE_GENERATED}
  ${CRANE_THEORIES_CPP})
target_link_libraries(spreadsheet PRIVATE imgui)
target_compile_options(spreadsheet PRIVATE
  -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable)
