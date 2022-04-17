open Core
open Core_bench

(* let () =
  Command_unix.run
    (Command.group
       ~summary:"Benchmarks"
       [ "infer", Benchmark_infer.command
       ; "stress-infer", Benchmark_infer.stress_command
       ]) *)

let perform_benchmark tests =
  let open Bench in
  Bench.bench
    ~run_config:
      (Run_config.create
         ~quota:(Quota.Num_calls 200)
         ~stabilize_gc_between_runs:true
         ~fork_each_benchmark:true
         ())
    ~save_to_file:(fun measurement ->
      "results/" ^ Measurement.name measurement ^ ".csv")
    ~analysis_configs:
      (Analysis_config.default
      |> List.map
           ~f:(Analysis_config.with_error_estimation ~bootstrap_trials:20))
    tests


let () = perform_benchmark Benchmark_infer.stress_tests
