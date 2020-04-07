
session UnionFind = HOL + 
  sessions
    Automatic_Refinement
    Collections
    "HOL-Library"
    Imperative_HOL_Time
  theories
    Union_Find_Time_alpha_verification

session UnionFind_Snippets in "UnionFind_Snippets" = HOL +
  options [
      document = "pdf",
      document_output = "generated"]
  sessions
    UnionFind
  theories
    "UnionFind.Union_Find_Time_alpha_fix"
  document_files
    build

