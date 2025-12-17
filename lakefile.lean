import Lake
open Lake DSL

package NjimaLean where

@[default_target]
lean_lib NjimaLean

@[default_target]
lean_exe njimaLean where
  root := `Main
