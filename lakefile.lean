import Lake
open Lake DSL

package «learninglean4» where
  -- Add package configuration options here

@[default_target]
lean_exe «learninglean4» where
  root := `learning_lean4_session_7
  supportInterpreter := true

lean_exe session1 where
  root := `learning_lean4_session_1

lean_exe session2 where
  root := `learning_lean4_session_2

lean_exe session3 where
  root := `learning_lean4_session_3

lean_exe session4 where
  root := `learning_lean4_session_4

lean_exe session5 where
  root := `learning_lean4_session_5

lean_exe session6 where
  root := `learning_lean4_session_6

lean_exe session7 where
  root := `learning_lean4_session_7

lean_exe session8 where
  root := `learning_lean4_session_8

lean_exe session9 where
  root := `learning_lean4_session_9

lean_lib learning_lean4_session_9

lean_exe session10 where
  root := `learning_lean4_session_10

lean_lib learning_lean4_session_10

lean_exe session11 where
  root := `learning_lean4_session_11
