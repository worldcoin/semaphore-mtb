import Lake
open Lake DSL

package «formal-verification» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"26d0eab43f05db777d1cf31abd31d3a57954b2a9"

require ProvenZK from git
  "https://github.com/reilabs/proven-zk.git"@"5f42162cb52c80315389c4f9a5d5e4782531e919"

lean_lib FormalVerification {
  moreLeanArgs := #["--tstack=65520", "-DmaxRecDepth=10000", "-DmaxHeartbeats=200000000"]
  -- add library configuration options here
}

@[default_target]
lean_exe «formal-verification» {
  root := `Main
}
