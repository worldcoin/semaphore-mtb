import Lake
open Lake DSL

package «formal-verification» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"26d0eab43f05db777d1cf31abd31d3a57954b2a9"

require ProvenZK from git
  "https://github.com/reilabs/proven-zk.git"@"v1.0.0"

lean_lib FormalVerification {
  moreLeanArgs := #["--tstack=10000000", "-DmaxRecDepth=6000", "-DmaxHeartbeats=0"]
  -- add library configuration options here
}

@[default_target]
lean_exe «formal-verification» {
  root := `Main
}
