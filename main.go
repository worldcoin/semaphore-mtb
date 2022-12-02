package main

import (
	"fmt"
	"github.com/urfave/cli/v2"
	"io"
	"math/big"
	"os"
)

//func fromHex(s string) big.Int {
//	var bi big.Int
//	bi.SetString(s, 0)
//	return bi
//}

//func toBytesLE(b []byte) []byte {
//	for i := 0; i < len(b)/2; i++ {
//		b[i], b[len(b)-i-1] = b[len(b)-i-1], b[i]
//	}
//	return b
//}

//func test() {
//	logger.Set(logger.Logger().Level(-1))
//	log := logger.Logger()
//	var startIndex uint32 = 1
//	dummyIdComm := fromHex("0x0000000000000000000000000000000000000000000000000000000000000000")
//	dummyProof := [20]frontend.Variable{
//		fromHex("0x0000000000000000000000000000000000000000000000000000000000000000"),
//		fromHex("0x2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864"),
//		fromHex("0x1069673dcdb12263df301a6ff584a7ec261a44cb9dc68df067a4774460b1f1e1"),
//		fromHex("0x18f43331537ee2af2e3d758d50f72106467c6eea50371dd528d57eb2b856d238"),
//		fromHex("0x07f9d837cb17b0d36320ffe93ba52345f1b728571a568265caac97559dbc952a"),
//		fromHex("0x2b94cf5e8746b3f5c9631f4c5df32907a699c58c94b2ad4d7b5cec1639183f55"),
//		fromHex("0x2dee93c5a666459646ea7d22cca9e1bcfed71e6951b953611d11dda32ea09d78"),
//		fromHex("0x078295e5a22b84e982cf601eb639597b8b0515a88cb5ac7fa8a4aabe3c87349d"),
//		fromHex("0x2fa5e5f18f6027a6501bec864564472a616b2e274a41211a444cbe3a99f3cc61"),
//		fromHex("0x0e884376d0d8fd21ecb780389e941f66e45e7acce3e228ab3e2156a614fcd747"),
//		fromHex("0x1b7201da72494f1e28717ad1a52eb469f95892f957713533de6175e5da190af2"),
//		fromHex("0x1f8d8822725e36385200c0b201249819a6e6e1e4650808b5bebc6bface7d7636"),
//		fromHex("0x2c5d82f66c914bafb9701589ba8cfcfb6162b0a12acf88a8d0879a0471b5f85a"),
//		fromHex("0x14c54148a0940bb820957f5adf3fa1134ef5c4aaa113f4646458f270e0bfbfd0"),
//		fromHex("0x190d33b12f986f961e10c0ee44d8b9af11be25588cad89d416118e4bf4ebe80c"),
//		fromHex("0x22f98aa9ce704152ac17354914ad73ed1167ae6596af510aa5b3649325e06c92"),
//		fromHex("0x2a7c7c9b6ce5880b9f6f228d72bf6a575a526f29c66ecceef8b753d38bba7323"),
//		fromHex("0x2e8186e558698ec1c67af9c14d463ffc470043c9c2988b954d75dd643f36b992"),
//		fromHex("0x0f57c5571e9a4eab49e2c8cf050dae948aef6ead647392273546249d1c1ff10f"),
//		fromHex("0x1830ee67b5fb554ad5f63d4388800e1cfe78e310697d46e43c9ce36134f72cca"),
//	}
//
//	idComms := [batchSize]frontend.Variable{}
//	for i := 0; i < batchSize; i++ {
//		idComms[i] = dummyIdComm
//	}
//
//	proofs := [batchSize][depth]frontend.Variable{}
//	for i := 0; i < batchSize; i++ {
//		proofs[i] = dummyProof
//	}
//
//	preRoot := fromHex("0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e")
//	postRoot := fromHex("0x2134e76ac5d21aab186c2be1dd8f84ee880a1e46eaf712f9d371b6df22191f3e")
//
//	// hash public inputs
//	data := []byte{}
//	// startIndex
//	buf := new(bytes.Buffer)
//	binary.Write(buf, binary.LittleEndian, startIndex)
//	data = append(data, buf.Bytes()...)
//	// pre and post root
//	data = append(data, toBytesLE(preRoot.Bytes())...)
//	data = append(data, toBytesLE(postRoot.Bytes())...)
//	// idComms
//	for i := 0; i < batchSize; i++ {
//		tmp := toBytesLE(dummyIdComm.Bytes())
//		// extend to 32 bytes if necessary
//		if len(dummyIdComm.Bytes()) < 32 {
//			tmp = append(tmp, make([]byte, 32-len(dummyIdComm.Bytes()))...)
//		}
//		data = append(data, tmp...)
//	}
//	hashBytes := toBytesLE(crypto.Keccak256Hash(data).Bytes())
//	var hash big.Int
//	hash.SetBytes(hashBytes)
//
//	Logger().Debug().Msg("Compiling circuit")
//
//	// compiles our circuit into a R1CS
//	var circuit MbuCircuit
//	ccs, _ := frontend.Compile(ecc.BN254, r1cs.NewBuilder, &circuit)
//
//	Logger().Debug().Msg("Setting up circuit")
//
//	// groth16 zkSNARK: Setup
//	_, _, _ = groth16.Setup(ccs)
//
//	//// witness definition
//	//assignment := MbuCircuit{
//	//	// public inputs
//	//	InputHash: hash,
//	//
//	//	// hashed private inputs
//	//	StartIndex: startIndex,
//	//	PreRoot:    preRoot,
//	//	PostRoot:   postRoot,
//	//	IdComms:    idComms,
//	//
//	//	// private inputs
//	//	MerkleProofs: proofs,
//	//}
//	//
//	//Logger().Debug().Msg("Proving")
//	//
//	//start := time.Now()
//	//witness, _ := frontend.NewWitness(&assignment, ecc.BN254)
//	//_, err := witness.Public()
//	//if err != nil {
//	//	panic(err)
//	//}
//	//fmt.Println("Witness generation took:", time.Since(start))
//	//
//	//start = time.Now()
//	//_, err = groth16.Prove(ccs, pk, witness)
//	//fmt.Println("Proof generation took:", time.Since(start))
//	//
//	//if err == nil {
//	//	println("Proof generated successfully.")
//	//}
//
//	// groth16.Verify(proof, vk, publicWitness)
//}

func main() {
	app := cli.App{
		EnableBashCompletion: true,
		Commands: []*cli.Command{
			{
				Name: "setup",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "output", Usage: "Output file", Required: true},
					&cli.UintFlag{Name: "tree-depth", Usage: "Merkle tree depth", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "Batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					path := context.String("output")
					treeDepth := uint32(context.Uint("tree-depth"))
					batchSize := uint32(context.Uint("batch-size"))
					Logger().Info().Msg("Running setup")
					system, err := Setup(treeDepth, batchSize)
					file, err := os.Create(path)
					defer file.Close()
					if err != nil {
						return err
					}
					written, err := system.WriteTo(file)
					if err != nil {
						return err
					}
					Logger().Info().Int64("bytesWritten", written).Msg("proving system written to file")
					return nil
				},
			},
			{
				Name: "export-solidity",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
					&cli.StringFlag{Name: "output", Usage: "solidity output (will write to stdout if not provided)", Required: false},
				},
				Action: func(context *cli.Context) error {
					keys := context.String("keys-file")
					ps, err := ReadSystemFromFile(keys)
					if err != nil {
						return err
					}
					var output io.Writer
					if outPath := context.String("output"); outPath != "" {
						file, err := os.Create(outPath)
						defer file.Close()
						if err != nil {
							return err
						}
						output = file
					} else {
						output = os.Stdout
					}
					return ps.ExportSolidity(output)
				},
			},
			{
				Name: "gen-test-params",
				Flags: []cli.Flag{
					&cli.UintFlag{Name: "tree-depth", Usage: "depth of the mock tree", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					treeDepth := context.Int("tree-depth")
					//batchSize := uint32(context.Uint("batch-size"))
					Logger().Info().Msg("Generating test params")

					tree := NewTree(treeDepth)
					println(len(tree.Contents))
					println(toHex(&tree.Contents[1]))
					r := tree.Update(0, big.Int{})
					println(len(r))
					sr := make([]string, len(r))
					for i, v := range r {
						sr[i] = toHex(&v)
						fmt.Println(sr[i])
					}
					return nil
				},
			},
			//{
			//	Name: "prove",
			//	Flags: []cli.Flag{
			//		&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
			//	},
			//	Action: func(context *cli.Context) error {
			//		keys := context.String("keys-file")
			//		ps, err := ReadSystemFromFile(keys)
			//		if err != nil {
			//			return err
			//		}
			//		Logger().Info().Uint32("treeDepth", ps.TreeDepth).Uint32("batchSize", ps.BatchSize).Msg("Read proving system")
			//
			//	},
			//},
		},
	}

	if err := app.Run(os.Args); err != nil {
		Logger().Fatal().Err(err).Msg("App failed.")
	}
}
