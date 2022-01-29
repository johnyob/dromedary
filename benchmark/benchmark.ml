open Core

let () =
  Command_unix.run
    (Command.group ~summary:"Benchmarks" [ "infer", Benchmark_infer.command ])
