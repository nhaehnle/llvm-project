
llvm_add_library(MLIRTableGen
  Argument.cpp
  Attribute.cpp
  AttrOrTypeDef.cpp
  Builder.cpp
  Class.cpp
  CodeGenHelpers.cpp
  Constraint.cpp
  Dialect.cpp
  Format.cpp
  GenInfo.cpp
  Interfaces.cpp
  Operator.cpp
  Pass.cpp
  Pattern.cpp
  Predicate.cpp
  Region.cpp
  SideEffects.cpp
  Successor.cpp
  Trait.cpp
  Type.cpp

  ADDITIONAL_HEADER_DIRS
  ${MLIR_MAIN_INCLUDE_DIR}/mlir/TableGen
)

mlir_check_all_link_libraries(MLIRTableGen)

add_mlir_library_install(MLIRTableGen)
