import Lake
open Lake DSL

/- copied from old eternity2 cadical impl
  https://github.com/JamesGallicchio/eternity2/blob/c0e868a883aabb6b53b7bc8a86434cee5f295777/lean/lakefile.lean
-/
/-- Compute the path to `libstdc++.so.6` by running `whereis` -/
elab "#get_libstdcpp" : command =>
  open Lean Elab Command Term in do
  let defLib (term : Expr) :=
    liftTermElabM <| addAndCompile <| Declaration.defnDecl {
        name := "libstdcpp"
        levelParams := []
        type := mkApp (mkConst ``Option [.zero]) (mkConst ``System.FilePath)
        value := term
        hints := .abbrev
        safety := .safe
      }
  if System.Platform.isOSX then
    defLib (mkApp (mkConst ``none [.zero]) (mkConst ``System.FilePath))
    return
  let output ← IO.Process.run {
    cmd := "whereis"
    args := #["libstdc++.so.6"]
  }
  match output.split (·.isWhitespace) with
  | name :: loc :: _ =>
    logInfo s!"found {name} at {loc}"
    defLib (mkAppN (mkConst ``some [.zero]) #[
      mkConst ``System.FilePath,
      mkApp (mkConst ``System.FilePath.mk) (mkStrLit loc)])
  | _ =>
    logError ("whereis output malformed:\n" ++ output)

#get_libstdcpp -- now available as `libstdcpp` declaration

package «DateTime» where
  precompileModules := true
  moreLinkArgs := match libstdcpp with | none => #[] | some x => #[x.toString]
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
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-lc++"]
  buildO "datetime.cpp" oFile srcJob flags #[] "cc"

extern_lib libleandatetime pkg := do
  let name := nameToStaticLib "datetime"
  let datetimeO ← fetch <| pkg.target ``datetime.o
  buildStaticLib (pkg.nativeLibDir / name) #[datetimeO]
