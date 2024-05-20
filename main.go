package main

import (
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"os/signal"

	"worldcoin/gnark-mbu/logging"
	poseidon "worldcoin/gnark-mbu/poseidon_native"
	"worldcoin/gnark-mbu/prover"
	"worldcoin/gnark-mbu/server"

	"github.com/consensys/gnark/constraint"
	gnarkLogger "github.com/consensys/gnark/logger"
	"github.com/urfave/cli/v2"
)

func main() {
	gnarkLogger.Set(*logging.Logger())
	app := cli.App{
		EnableBashCompletion: true,
		Commands: []*cli.Command{
			{
				Name: "setup",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.StringFlag{Name: "output", Usage: "Output file", Required: true},
					&cli.UintFlag{Name: "tree-depth", Usage: "Merkle tree depth", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "Batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					mode := context.String("mode")

					path := context.String("output")
					treeDepth := uint32(context.Uint("tree-depth"))
					batchSize := uint32(context.Uint("batch-size"))
					logging.Logger().Info().Msg("Running setup")

					var system *prover.ProvingSystem
					var err error
					if mode == server.InsertionMode {
						system, err = prover.SetupInsertion(treeDepth, batchSize)
					} else if mode == server.DeletionMode {
						system, err = prover.SetupDeletion(treeDepth, batchSize)
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}

					if err != nil {
						return err
					}
					file, err := os.Create(path)
					defer file.Close()
					if err != nil {
						return err
					}
					written, err := system.WriteTo(file)
					if err != nil {
						return err
					}
					logging.Logger().Info().Int64("bytesWritten", written).Msg("proving system written to file")
					return nil
				},
			},
			{
				Name: "r1cs",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.StringFlag{Name: "output", Usage: "Output file", Required: true},
					&cli.UintFlag{Name: "tree-depth", Usage: "Merkle tree depth", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "Batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					mode := context.String("mode")

					path := context.String("output")
					treeDepth := uint32(context.Uint("tree-depth"))
					batchSize := uint32(context.Uint("batch-size"))
					logging.Logger().Info().Msg("Building R1CS")

					var cs constraint.ConstraintSystem
					var err error

					if mode == server.InsertionMode {
						cs, err = prover.BuildR1CSInsertion(treeDepth, batchSize)
					} else if mode == server.DeletionMode {
						cs, err = prover.BuildR1CSDeletion(treeDepth, batchSize)
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}

					if err != nil {
						return err
					}
					file, err := os.Create(path)
					defer file.Close()
					if err != nil {
						return err
					}
					written, err := cs.WriteTo(file)
					if err != nil {
						return err
					}
					logging.Logger().Info().Int64("bytesWritten", written).Msg("R1CS written to file")
					return nil
				},
			},
			{
				Name: "import-setup",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "output", Usage: "Output file", Required: true},
					&cli.StringFlag{Name: "pk", Usage: "Proving key", Required: true},
					&cli.StringFlag{Name: "vk", Usage: "Verifying key", Required: true},
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", Required: true},
					&cli.UintFlag{Name: "tree-depth", Usage: "Merkle tree depth", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "Batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					path := context.String("output")
					pk := context.String("pk")
					vk := context.String("vk")
					mode := context.String("mode")
					treeDepth := uint32(context.Uint("tree-depth"))
					batchSize := uint32(context.Uint("batch-size"))
					var system *prover.ProvingSystem
					var err error

					logging.Logger().Info().Msg("Importing setup")

					if mode == server.InsertionMode {
						system, err = prover.ImportInsertionSetup(treeDepth, batchSize, pk, vk)

						if err != nil {
							return err
						}

					} else if mode == server.DeletionMode {
						system, err = prover.ImportDeletionSetup(treeDepth, batchSize, pk, vk)

						if err != nil {
							return err
						}
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}
					file, err := os.Create(path)
					defer file.Close()
					if err != nil {
						return err
					}
					written, err := system.WriteTo(file)
					if err != nil {
						return err
					}
					logging.Logger().Info().Int64("bytesWritten", written).Msg("proving system written to file")
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
					ps, err := prover.ReadSystemFromFile(keys)
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
				Name: "export-vk",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
					&cli.StringFlag{Name: "output", Usage: "output file", Required: true},
				},
				Action: func(context *cli.Context) error {
					keys := context.String("keys-file")
					ps, err := prover.ReadSystemFromFile(keys)
					if err != nil {
						return err
					}
					outPath := context.String("output")

					file, err := os.Create(outPath)
					defer file.Close()
					if err != nil {
						return err
					}
					output := file
					_, err = ps.VerifyingKey.WriteTo(output)
					return err
				},
			},
			{
				Name: "gen-test-params",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.UintFlag{Name: "tree-depth", Usage: "depth of the mock tree", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					mode := context.String("mode")

					treeDepth := context.Int("tree-depth")
					batchSize := uint32(context.Uint("batch-size"))
					logging.Logger().Info().Msg("Generating test params for the insertion circuit")

					var r []byte
					var err error

					if mode == server.InsertionMode {
						params := prover.InsertionParameters{}
						tree := poseidon.NewTree(treeDepth)

						params.StartIndex = 0
						params.PreRoot = tree.Root()
						params.IdComms = make([]big.Int, batchSize)
						params.MerkleProofs = make([][]big.Int, batchSize)
						for i := 0; i < int(batchSize); i++ {
							params.IdComms[i] = *new(big.Int).SetUint64(uint64(i + 1))
							params.MerkleProofs[i] = tree.Update(i, params.IdComms[i])
						}
						params.PostRoot = tree.Root()
						params.ComputeInputHashInsertion()
						r, err = json.Marshal(&params)
					} else if mode == server.DeletionMode {
						params := prover.DeletionParameters{}
						tree := poseidon.NewTree(treeDepth)

						params.DeletionIndices = make([]uint32, batchSize)
						params.IdComms = make([]big.Int, batchSize)
						params.MerkleProofs = make([][]big.Int, batchSize)
						for i := 0; i < int(batchSize*2); i++ {
							tree.Update(i, *new(big.Int).SetUint64(uint64(i + 1)))
						}
						params.PreRoot = tree.Root()
						for i := 0; i < int(batchSize); i++ {
							params.DeletionIndices[i] = uint32(2 * i)
							params.IdComms[i] = *new(big.Int).SetUint64(uint64(2*i + 1))
							params.MerkleProofs[i] = tree.Update(2*i, *big.NewInt(0))
						}
						params.PostRoot = tree.Root()
						params.ComputeInputHashDeletion()
						r, err = json.Marshal(&params)
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}

					if err != nil {
						return err
					}

					fmt.Println(string(r))
					return nil
				},
			},
			{
				Name: "start",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
					&cli.BoolFlag{Name: "json-logging", Usage: "enable JSON logging", Required: false},
					&cli.StringFlag{Name: "prover-address", Usage: "address for the prover server", Value: "localhost:3001", Required: false},
					&cli.StringFlag{Name: "metrics-address", Usage: "address for the metrics server", Value: "localhost:9998", Required: false},
				},
				Action: func(context *cli.Context) error {
					if context.Bool("json-logging") {
						logging.SetJSONOutput()
					}
					keys := context.String("keys-file")
					mode := context.String("mode")

					if mode != server.DeletionMode && mode != server.InsertionMode {
						return fmt.Errorf("invalid mode: %s", mode)
					}

					logging.Logger().Info().Msg("Reading proving system from file")
					ps, err := prover.ReadSystemFromFile(keys)
					if err != nil {
						return err
					}
					logging.Logger().Info().Uint32("treeDepth", ps.TreeDepth).Uint32("batchSize", ps.BatchSize).Msg("Read proving system")
					config := server.Config{
						ProverAddress:  context.String("prover-address"),
						MetricsAddress: context.String("metrics-address"),
						Mode:           mode,
					}
					instance := server.Run(&config, ps)
					sigint := make(chan os.Signal, 1)
					signal.Notify(sigint, os.Interrupt)
					<-sigint
					logging.Logger().Info().Msg("Received sigint, shutting down")
					instance.RequestStop()
					logging.Logger().Info().Msg("Waiting for server to close")
					instance.AwaitStop()
					return nil
				},
			},
			{
				Name: "prove",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
				},
				Action: func(context *cli.Context) error {
					mode := context.String("mode")

					keys := context.String("keys-file")
					ps, err := prover.ReadSystemFromFile(keys)
					if err != nil {
						return err
					}
					logging.Logger().Info().Uint32("treeDepth", ps.TreeDepth).Uint32("batchSize", ps.BatchSize).Msg("Read proving system")
					logging.Logger().Info().Msg("reading params from stdin")
					bytes, err := io.ReadAll(os.Stdin)
					if err != nil {
						return err
					}

					var proof *prover.Proof
					if mode == server.InsertionMode {
						var params prover.InsertionParameters
						err = json.Unmarshal(bytes, &params)
						if err != nil {
							return err
						}
						logging.Logger().Info().Msg("params read successfully")
						proof, err = ps.ProveInsertion(&params)
					} else if mode == server.DeletionMode {
						var params prover.DeletionParameters
						err = json.Unmarshal(bytes, &params)
						if err != nil {
							return err
						}
						logging.Logger().Info().Msg("params read successfully")
						proof, err = ps.ProveDeletion(&params)
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}

					if err != nil {
						return err
					}
					r, _ := json.Marshal(&proof)
					fmt.Println(string(r))
					return nil
				},
			},
			{
				Name: "verify",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "mode", Usage: "insertion/deletion", EnvVars: []string{"MTB_MODE"}, DefaultText: "insertion"},
					&cli.StringFlag{Name: "keys-file", Usage: "proving system file", Required: true},
					&cli.StringFlag{Name: "input-hash", Usage: "the hash of all public inputs", Required: true},
				},
				Action: func(context *cli.Context) error {
					mode := context.String("mode")

					keys := context.String("keys-file")
					var inputHash big.Int
					_, ok := inputHash.SetString(context.String("input-hash"), 0)
					if !ok {
						return fmt.Errorf("invalid number: %s", context.String("input-hash"))
					}
					ps, err := prover.ReadSystemFromFile(keys)
					if err != nil {
						return err
					}
					logging.Logger().Info().Uint32("treeDepth", ps.TreeDepth).Uint32("batchSize", ps.BatchSize).Msg("Read proving system")
					logging.Logger().Info().Msg("reading proof from stdin")
					bytes, err := io.ReadAll(os.Stdin)
					if err != nil {
						return err
					}
					var proof prover.Proof
					err = json.Unmarshal(bytes, &proof)
					if err != nil {
						return err
					}
					logging.Logger().Info().Msg("proof read successfully")

					if mode == server.InsertionMode {
						err = ps.VerifyInsertion(inputHash, &proof)
					} else if mode == server.DeletionMode {
						err = ps.VerifyDeletion(inputHash, &proof)
					} else {
						return fmt.Errorf("Invalid mode: %s", mode)
					}

					if err != nil {
						return err
					}
					logging.Logger().Info().Msg("verification complete")
					return nil
				},
			},
			{
				Name: "extract-circuit",
				Flags: []cli.Flag{
					&cli.StringFlag{Name: "output", Usage: "Output file", Required: true},
					&cli.UintFlag{Name: "tree-depth", Usage: "Merkle tree depth", Required: true},
					&cli.UintFlag{Name: "batch-size", Usage: "Batch size", Required: true},
				},
				Action: func(context *cli.Context) error {
					path := context.String("output")
					treeDepth := uint32(context.Uint("tree-depth"))
					batchSize := uint32(context.Uint("batch-size"))
					logging.Logger().Info().Msg("Extracting gnark circuit to Lean")
					circuit_string, err := prover.ExtractLean(treeDepth, batchSize)
					if err != nil {
						return err
					}
					file, err := os.Create(path)
					defer file.Close()
					if err != nil {
						return err
					}
					written, err := file.WriteString(circuit_string)
					if err != nil {
						return err
					}
					logging.Logger().Info().Int("bytesWritten", written).Msg("Lean circuit written to file")

					return nil
				},
			},
		},
	}

	if err := app.Run(os.Args); err != nil {
		logging.Logger().Fatal().Err(err).Msg("App failed.")
	}
}
