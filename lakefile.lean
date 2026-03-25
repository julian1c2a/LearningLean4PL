import Lake
open Lake DSL

package «learninglean4» where
  -- Add package configuration options here

@[default_target]
lean_exe «learninglean4» where
  -- Apuntamos al archivo que contiene nuestra función `main`
  root := `learning_lean4_session_1
  -- Enables the Lean interpreter to find the executable's source code and imports,
  -- enabling commands like `#eval` and code completion in the source file.
  supportInterpreter := true
