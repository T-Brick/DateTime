import Lake
open Lake DSL

package «DateTime» where
  precompileModules := true
  -- add package configuration options here

lean_lib «DateTime» where
  -- add library configuration options here

@[default_target]
lean_exe «datetime» where
  root := `Main
  supportInterpreter := true

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "DateTime" / "c" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "DateTime" / "c"  / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO "ffi.cpp" oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi pkg := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← fetch <| pkg.target ``ffi.o
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
