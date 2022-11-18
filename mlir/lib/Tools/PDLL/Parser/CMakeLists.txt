
llvm_add_library(MLIRPDLLParser STATIC
  CodeComplete.cpp
  Lexer.cpp
  Parser.cpp
  
  LINK_COMPONENTS
  Support
  TableGen

  LINK_LIBS PUBLIC
  MLIRPDLLAST
  MLIRSupport
  MLIRTableGen
  )
