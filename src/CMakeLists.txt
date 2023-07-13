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

add_executable(md
  md.cpp
)

target_link_libraries(md ${LIBS})

llvm_update_compile_flags(md)

mlir_check_all_link_libraries(md)

# add_executable(dataflow
#   dataflow.cpp
# )
# 
# target_link_libraries(dataflow ${LIBS})
# 
# llvm_update_compile_flags(dataflow)
# 
# mlir_check_all_link_libraries(dataflow)
