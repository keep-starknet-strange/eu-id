WO: WO-1.2 cross-module fan-out

## Blocker

I attempted the spec's minimal trait split in `air_core::AirProver`: pure
`gen_preprocessed_columns` / `gen_trace_columns` / `gen_interaction_columns`
methods, with `air_core::prove` collecting per-module column vectors via
`rayon::par_iter_mut()` and then extending each `TreeBuilder` serially in module
order.

This does not compile safely because the current prover module types are not
`Send`:

- `SharedRelation<R>` is `Rc<RefCell<Option<R>>>`, so P256/SHA/bridge/age/nat
  provers carrying shared relation handles cannot cross Rayon worker threads.
- Several prover structs carry optional built Stwo `FrameworkComponent` values;
  those contain `Rc<RefCell<ArithmeticCounts>>` through Stwo's
  `InfoEvaluator`, also making the full prover structs non-`Send`.

The interaction phase also reads shared relation handles, so simply adding
`unsafe impl Send` for the prover structs would be too broad unless we first
separate the thread-local column-generation state from transcript/component
state.

## Question

Which architecture do you want for WO-1.2?

1. Convert `SharedRelation` to a thread-safe `Arc<Mutex<Option<R>>>` (or similar)
   and split built components out of the data moved through Rayon.
2. Add explicit per-module "column task" structs that contain only Send column
   inputs, leaving `AirProver` itself serial and non-Send.
3. Treat WO-1.2 as blocked/out of scope because the safe fan-out requires a
   larger orchestrator refactor than the WO text implies.

I reverted the failed implementation attempt and did not change production code.
