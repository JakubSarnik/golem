cmake_minimum_required(VERSION 3.14)

set(GOLEM_VERSION_MAJOR 0)
set(GOLEM_VERSION_MINOR 9)
set(GOLEM_VERSION_PATCH 1)
set(GOLEM_VERSION ${GOLEM_VERSION_MAJOR}.${GOLEM_VERSION_MINOR}.${GOLEM_VERSION_PATCH})
project(Golem VERSION ${GOLEM_VERSION} LANGUAGES CXX)

add_definitions(-DGOLEM_VERSION="${GOLEM_VERSION}")

set(CMAKE_CXX_STANDARD 20)

set(CMAKE_SOURCE_DIR "src")

set(VALID_BUILD_TYPES "Debug" "Release" "RelWithDebInfo" "MinSizeRel")

#Set the default build type if this is the first time cmake is run and nothing has been set
if (NOT EXISTS ${CMAKE_BINARY_DIR}/CMakeCache.txt)
  if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Choose the type of build, options are: Debug Release RelWithDebInfo MinSizeRel." FORCE)
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${VALID_BUILD_TYPES})
  endif()
endif()

list(FIND VALID_BUILD_TYPES "${CMAKE_BUILD_TYPE}" _build_type_index)
if(_build_type_index EQUAL -1)
  message(FATAL_ERROR "Invalid build type: ${CMAKE_BUILD_TYPE}. Valid options are: ${VALID_BUILD_TYPES}")
endif()

option(GOLEM_BUILD_TEST "Build the tests" ON)

# On macOS, search Homebrew for keg-only versions of Bison and Flex. Xcode does
# not provide new enough versions for us to use.
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    execute_process(
            COMMAND brew --prefix bison
            RESULT_VARIABLE BREW_BISON
            OUTPUT_VARIABLE BREW_BISON_PREFIX
            OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_BISON EQUAL 0 AND EXISTS "${BREW_BISON_PREFIX}")
        message(STATUS "Found Bison keg installed by Homebrew at ${BREW_BISON_PREFIX}")
        set(BISON_EXECUTABLE "${BREW_BISON_PREFIX}/bin/bison")
    endif()

    execute_process(
            COMMAND brew --prefix flex
            RESULT_VARIABLE BREW_FLEX
            OUTPUT_VARIABLE BREW_FLEX_PREFIX
            OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_FLEX EQUAL 0 AND EXISTS "${BREW_FLEX_PREFIX}")
        message(STATUS "Found Flex keg installed by Homebrew at ${BREW_FLEX_PREFIX}")
        set(FLEX_EXECUTABLE "${BREW_FLEX_PREFIX}/bin/flex")
    endif()
endif()

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
if(GOLEM_BUILD_TEST)
    enable_testing()
    add_subdirectory(${PROJECT_SOURCE_DIR}/test)
endif()
#########################################################################
