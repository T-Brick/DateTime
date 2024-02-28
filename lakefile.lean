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

target datetime.o pkg : FilePath := do
  let oFile := pkg.buildDir / "DateTime" / "c" / "datetime.o"
  let srcJob ← inputFile <| pkg.dir / "DateTime" / "c"  / "datetime.cpp"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-lstdc++", "-Wl"]
  buildO "datetime.cpp" oFile srcJob flags #[] "g++"

extern_lib libleandatetime pkg := do
  let name := nameToStaticLib "datetime"
  let datetimeO ← fetch <| pkg.target ``datetime.o
  buildStaticLib (pkg.nativeLibDir / name) #[datetimeO]
