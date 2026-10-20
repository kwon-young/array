cmake_minimum_required(VERSION 3.20)
project(array C)

# The foreign libraries loaded by the Prolog modules.
# Build them before starting Prolog:
#
#   cmake -B build -DCMAKE_PREFIX_PATH=<swipl install prefix>
#   cmake --build build

find_package(SWIPL REQUIRED)

# A foreign library is loaded into swipl, which provides libswipl's symbols.
function(add_foreign_library name)
  add_library(${name} MODULE ${ARGN})
  set_target_properties(${name} PROPERTIES PREFIX "")
  target_include_directories(${name} PRIVATE
    $<TARGET_PROPERTY:swipl::libswipl,INTERFACE_INCLUDE_DIRECTORIES>)
endfunction()

# buffer.c includes the type conversions gen_type.pl generates.
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_SOURCE_DIR}/buffer_types.h
  COMMAND swipl::swipl -f none -g main -t halt gen_type.pl
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
  DEPENDS gen_type.pl c99.pl)
add_foreign_library(buffer buffer.c ${CMAKE_CURRENT_SOURCE_DIR}/buffer_types.h)
