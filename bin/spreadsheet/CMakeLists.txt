# Copyright 2026 Bloomberg Finance L.P.
# Distributed under the terms of the GNU LGPL v2.1 license.
#
# Build for the Crane spreadsheet demo: a Rocq-extracted spreadsheet kernel
# driven by a Dear ImGui front-end.
#
# Expects `dune build` to have produced Spreadsheet.h / Spreadsheet.cpp
# alongside this CMakeLists (the bin/spreadsheet/dune coq.theory writes
# them here directly via -output-directory).

cmake_minimum_required(VERSION 3.20)
project(crane-spreadsheet CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

get_filename_component(CRANE_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../.." ABSOLUTE)
set(CRANE_THEORIES_CPP "${CRANE_ROOT}/theories/cpp")

set(GEN_DIR "${CMAKE_CURRENT_SOURCE_DIR}/Spreadsheet")
if(NOT EXISTS "${GEN_DIR}/Spreadsheet.cpp")
  message(FATAL_ERROR
    "Spreadsheet.cpp not found in ${GEN_DIR}.\n"
    "Run `dune build bin/spreadsheet` first.")
endif()

# --- Dependencies -----------------------------------------------------------

find_package(OpenGL REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(GLFW REQUIRED IMPORTED_TARGET glfw3)

include(FetchContent)
FetchContent_Declare(
  imgui
  GIT_REPOSITORY https://github.com/ocornut/imgui.git
  GIT_TAG        v1.91.5
  GIT_SHALLOW    TRUE)
FetchContent_MakeAvailable(imgui)

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
  ${GEN_DIR}/Spreadsheet.cpp)
target_include_directories(spreadsheet PRIVATE
  ${GEN_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CRANE_THEORIES_CPP})
target_link_libraries(spreadsheet PRIVATE imgui)
target_compile_options(spreadsheet PRIVATE
  -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable)
