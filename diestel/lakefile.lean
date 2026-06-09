import Lake
open Lake DSL

package diestel

require mathlib from "../twin-width/.lake/packages/mathlib"

@[default_target]
lean_lib Chapter01 where
  srcDir := "."

lean_lib Chapter02 where
  srcDir := "."
