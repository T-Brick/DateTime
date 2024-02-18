import Lake
open Lake DSL

package «DateTime» where
  -- add package configuration options here

lean_lib «DateTime» where
  -- add library configuration options here

@[default_target]
lean_exe «datetime» where
  root := `Main
