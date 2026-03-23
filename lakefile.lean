import Lake
open System Lake DSL

package «sampcert» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc1"

@[default_target]
lean_lib «SampCert» where
  extraDepTargets := #[`libleanffi]

lean_lib «FastExtract» where

lean_lib «VMC» where

meta if get_config? env = some "doc" then
  require «doc-gen4» from git
    "https://github.com/leanprover/doc-gen4" @ "main"

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "g++" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← fetch <| pkg.target ``ffi.o
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_exe test where
  root := `Test
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

lean_exe check where
  root := `SampCertCheck
  extraDepTargets := #[`libleanffi]
  moreLinkArgs := #["-L.lake/build/lib", "-lleanffi"]

lean_exe mk_all where
  root := `mk_all
  supportInterpreter := true
  weakLinkArgs := #["-lLake"]
