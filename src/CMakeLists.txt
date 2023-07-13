get_property(dialect_libs GLOBAL PROPERTY MLIR_DIALECT_LIBS)
get_property(conversion_libs GLOBAL PROPERTY MLIR_CONVERSION_LIBS)

set(LLVM_LINK_COMPONENTS
  Core
  Support
  AsmParser
  )

set(LIBS
  ${dialect_libs}
  ${conversion_libs}

  MLIRAffineAnalysis
  MLIRAnalysis
  MLIRDialect
  MLIROptLib
  MLIRParser
  MLIRPass
  MLIRTransforms
  MLIRTransformUtils
  MLIRSupport
  MLIRIR
)

# add_executable(foo
#   foo.cpp
# )
# 
# target_link_libraries(foo ${LIBS})
# 
# llvm_update_compile_flags(foo)
# 
# mlir_check_all_link_libraries(foo)

add_executable(dependence
  dependence.cpp
)

target_link_libraries(dependence ${LIBS})

llvm_update_compile_flags(dependence)

mlir_check_all_link_libraries(dependence)
