cmake_minimum_required(VERSION 3.16)

project(array LANGUAGES C)

# Generate compile_commands.json for clangd.
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# --- SWI-Prolog -------------------------------------------------------------
# pack_install sets SWIPL_HOME_DIR; a local build finds it from the swipl
# executable.  swipl.cmake provides target_link_swipl(), swipl_add_test() and
# the pack's per-architecture library directory, swipl_module_dir.
if(DEFINED ENV{SWIPL})
  set(SWIPL $ENV{SWIPL})
else()
  find_program(SWIPL swipl REQUIRED)
endif()
if(DEFINED ENV{SWIPL_HOME_DIR})
  set(SWIPL_HOME_DIR $ENV{SWIPL_HOME_DIR})
else()
  execute_process(
    COMMAND ${SWIPL} -g "current_prolog_flag(home,H),write(H)" -t halt
    OUTPUT_VARIABLE SWIPL_HOME_DIR
    OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

list(INSERT CMAKE_MODULE_PATH 0 ${SWIPL_HOME_DIR}/cmake)
include(swipl)

# --- OpenCL -----------------------------------------------------------------
find_package(OpenCL REQUIRED)

# --- targets ----------------------------------------------------------------
# buffer.c includes the type conversions src/gen_type.pl generates.
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/buffer_types.h
  COMMAND ${SWIPL} -f none -g main -t halt ${CMAKE_CURRENT_SOURCE_DIR}/src/gen_type.pl
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS src/gen_type.pl src/c99.pl)

add_library(buffer MODULE src/buffer.c ${CMAKE_CURRENT_BINARY_DIR}/buffer_types.h)
target_link_swipl(buffer)
target_include_directories(buffer PRIVATE ${CMAKE_CURRENT_BINARY_DIR})

add_library(opencl MODULE src/opencl.c)
target_link_swipl(opencl)
target_compile_definitions(opencl PRIVATE CL_TARGET_OPENCL_VERSION=300)
target_link_libraries(opencl PRIVATE OpenCL::OpenCL)

# The modules go to the pack's lib/<arch> in the source tree, where
# use_foreign_library(foreign(...)) finds them once the pack is attached, and
# where the tests look for them: the pack build runs the tests before install.
set_target_properties(buffer opencl PROPERTIES
  LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/${swipl_module_dir}
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/${swipl_module_dir})

install(TARGETS buffer opencl
        DESTINATION ${CMAKE_CURRENT_SOURCE_DIR}/${swipl_module_dir})

# --- tests ------------------------------------------------------------------
# test/test_array.pl runs every test/*.plt.
enable_testing()
swipl_add_test(array)
