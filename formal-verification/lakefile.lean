import Lake
open Lake DSL

package «formal-verification» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"26d0eab43f05db777d1cf31abd31d3a57954b2a9"

require ProvenZK from git
  "https://github.com/reilabs/proven-zk.git"@"25ab09ae7d83ab6f34db1f8af289f1f738497dc9"

-- require ProvenZk from ".."/".."/"proven-zk"

lean_lib FormalVerification {
  moreLeanArgs := #["--tstack=65520", "-DmaxRecDepth=10000", "-DmaxHeartbeats=200000000"]
  -- add library configuration options here
}

@[default_target]
lean_exe «formal-verification» {
  moreLeanArgs := #["--tstack=65520", "-DmaxRecDepth=10000", "-DmaxHeartbeats=200000000"]
  root := `Main
}
