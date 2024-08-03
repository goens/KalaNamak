import Lake
open Lake DSL

package "KalaNamak" where
  -- add package configuration options here

lean_lib «KalaNamak» where
  -- add library configuration options here

@[default_target]
lean_exe "kalanamak" where
  root := `Main
