# Predicates CLI

## prove

Generate a predicate proof and write it to disk.

```
cargo prove <predicate> [flags] [--output PATH]
```

`--output PATH` — proof output path (default: `./proof.bin`)

### Age

```
cargo prove age --dob YYYY-MM-DD [--date YYYY-MM-DD] [--min-age N] [--strategy bd|rc] [--output PATH]
```

| Flag | Description | Default |
|------|-------------|---------|
| `--dob` | Date of birth | required |
| `--date` | Current date | today |
| `--min-age` | Minimum age in years | `18` |
| `--strategy` | `bd` (bit decomposition) or `rc` (range check) | `rc` |
| `--output` | Proof output path | `./proof.bin` |

**Examples**

```bash
# Prove age >= 18 with today as current date
cargo prove age --dob 1990-01-01

# Prove age >= 21 with a fixed current date
cargo prove age --dob 1990-01-01 --min-age 21 --date 2026-05-22

# Use bit decomposition strategy, write proof to custom path
cargo prove age --dob 1990-01-01 --strategy bd --output /tmp/age.bin
```

---

## verify

Verify a proof read from disk.

```
cargo verify <predicate> [flags] [--input PATH]
```

`--input PATH` — proof file to verify (default: `./proof.bin`)

### Age

```
cargo verify age [--strategy bd|rc] [--input PATH]
```

| Flag | Description | Default |
|------|-------------|---------|
| `--strategy` | Must match the strategy used to prove | `rc` |
| `--input` | Proof file path | `./proof.bin` |

**Examples**

```bash
# Verify default proof file
cargo verify age

# Verify a bit decomposition proof from a custom path
cargo verify age --strategy bd --input /tmp/age.bin
```

---

## Profiling

Profiling aliases run `cargo instruments` with the Allocations template and write
both the trace and the proof file to `target/instruments/`.
Run `prove` before `verify` for each strategy.

| Alias | Description |
|-------|-------------|
| `cargo profile-prove-age-rc` | Profile age prove (range check) |
| `cargo profile-verify-age-rc` | Profile age verify (range check) |
| `cargo profile-prove-age-bd` | Profile age prove (bit decomposition) |
| `cargo profile-verify-age-bd` | Profile age verify (bit decomposition) |

```bash
cargo profile-prove-age-rc
cargo profile-verify-age-rc
```

Traces are saved to `target/instruments/` and opened automatically in Instruments.app.
