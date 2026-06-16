# Formats reference — FPGA (Aria-HDL) bridge

leanlift verifies FPGA designs authored in **Aria-HDL** (`../fpga-meta-compiler`)
by ingesting its hardware IR through a JSON bridge and projecting it onto the
existing model families (see [`PLAN-fpga.md`](./PLAN-fpga.md)). This page is the
bridge-schema reference.

## The path

```sh
aria-hdl --emit-ir-json design.ahdl > design.aria.json   # Aria side (zero-dep emitter)
lift fpga info design.aria.json                           # leanlift side (ingest + echo)
```

`lift fpga info` is the Phase-B **round-trip check**: it reads the export and
echoes a faithful summary — modules, ports, clock domains, **annotations**,
**formal properties**, pipeline, and timing. Exit `0` on a clean parse; `1` on a
malformed or unsupported-schema document. The verbs `check` / `prove` / `timing`
/ `equiv` land in later phases behind this same path.

## Schema `aria-ir-json/v1`

One JSON **object per module**, concatenated (a multi-module `.ahdl` emits a
stream). Every object is self-describing via its `schema` field. Wide integers
(`u128`/`i128`/`u64` literal payloads, `freq_hz`, `clock_freq`) are emitted as
**JSON strings** to avoid f64 precision loss; the reader accepts a number or a
numeric string for those fields.

```jsonc
{
  "schema": "aria-ir-json/v1",
  "id": 2,
  "name": "tcp_fsm",
  "ports": [
    {"id":0,"value":1,"name":"clk","ty":{"t":"clock"},"dir":"input","clock_domain":0}
  ],
  "clock_domains": [
    {"id":0,"name":"default","clock_signal":0,"reset_signal":null,"freq_hz":"125000000"}
  ],
  "annotations": [                         // ← module-level @-annotations, always exported
    {"kind":"clock_freq","value":"125000000"},
    {"kind":"max_error","value":0.001}
  ],
  "nodes": [
    {"id":5,"name":"state","kind":{"k":"register","ty":{...},"clock_domain":0,
      "reset_value":{...}|null,"enable":{...}|null,"next":{...}}},
    {"id":7,"name":"safe","kind":{"k":"formal_property","property":{  // ← formal props, always exported
      "kind":"assert","temporal":{"tt":"always"},"expr":{...},"name":"safe"}}}
  ],
  "pipeline": {"id":0,"num_stages":3,"latency":5,"initiation_interval":1,
               "flow_control":{"fc":"ready_valid"},"stages":[...]}  | null,
  "systolic": {"rows":8,"cols":8,"dataflow":"output_stationary",...} | null,
  "timing": {"c_slow_factor":1,"target_period_ns":8.0,"critical_path_ns":0.8,
             "retiming_weights":[...],"buffers":[...]}
}
```

### Tag conventions

- **Types** carry a `"t"` tag: `bit`, `bits`, `uint`, `sint`, `fixed`, `float`,
  `array`, `tuple`, `struct`, `enum`, `mx`, `clock`, `reset`, `void`.
- **Expressions** carry an `"e"` tag: `ref`, `lit`, `binop`, `unop`, `mux`,
  `casemux`, `bitslice`, `bitindex`, `concat`, `cast`, `arrayindex`,
  `structfield`, `structconstruct`, `enumconstruct`, `enumtag`, `enumpayload`,
  `reduce`, `approxlookup`. Literals carry an `"l"` tag.
- **Node kinds** carry a `"k"` tag: `wire`, `register`, `memory`, `instance`,
  `fifo`, `pipeline_reg`, `processing_element`, `approx_unit`, `formal_property`.
- **Annotations** (`kind`): `target`, `clock_freq`, `emulate`, `prove`,
  `max_luts`, `max_regs`, `max_dsp`, `max_bram`, `impl`, `max_error`.
- **Formal `temporal`** (`tt`): `combinational`, `always`, `never`, `eventually`,
  `next`(+`n`), `until`(+`holding`/`release`), `implies`(+`antecedent`/
  `consequent`/`next_cycle`). **`kind`**: `assert` | `assume` | `cover`.

## What each family will consume (later phases)

| Aria IR | → leanlift family | uses |
|---|---|---|
| enum-typed `register` + `mux`/`casemux` `next` | FSM | states, transitions, `assert`/`never` → `forbid` |
| `fifo` / `pipeline_reg` / ready-valid | Petri | occupancy place, `depth` → bound, loss transition |
| `pipeline` (`latency`, `initiation_interval`) + `clock_freq` | tasks | RTA latency bound |
| streaming `pipeline` / backpressure | qnet | throughput, bottleneck stage |
| channel loss | GSPN→CTMC | delivery probability, phase change |

The emitter is faithful by construction (`../fpga-meta-compiler/src/ir_json.rs`):
every IR variant has a tag and all of its fields, and **nothing is dropped** —
annotations and formal properties included. The leanlift reader is a
dependency-free JSON parser (`src/models/fpga.rs`, sibling to `xml.rs`).
