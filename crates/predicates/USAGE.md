# Predicates CLI

## prove-age

Generate an age predicate proof and write it to disk.

```
make prove-age [DOB=YYYY-MM-DD] [DATE=YYYY-MM-DD] [MIN_AGE=N] [STRATEGY=rc] [PROOF=PATH]
```

| Variable | Description | Default |
|----------|-------------|---------|
| `DOB` | Date of birth | required |
| `DATE` | Current date | today |
| `MIN_AGE` | Minimum age in years | `18` |
| `STRATEGY` | `rc` (range check) | `rc` |
| `PROOF` | Proof output path | `proof.bin` |

**Examples**

```bash
# Prove age >= 18 with today as current date
make prove-age DOB=1990-01-01

# Prove age >= 21 with a fixed current date
make prove-age DOB=1990-01-01 MIN_AGE=21 DATE=2026-05-22

# Write proof to custom path
make prove-age DOB=1990-01-01 STRATEGY=rc PROOF=/tmp/age.bin
```

---

## verify-age

Verify a proof read from disk.

```
make verify-age [STRATEGY=rc] [PROOF=PATH]
```

| Variable | Description | Default |
|----------|-------------|---------|
| `STRATEGY` | Must match the strategy used to prove | `rc` |
| `PROOF` | Proof file path | `proof.bin` |

**Examples**

```bash
# Verify default proof file
make verify-age

# Verify a proof from a custom path
make verify-age STRATEGY=rc PROOF=/tmp/age.bin
```

---

## Profiling

Profiling targets run `cargo instruments` with the Allocations template and write
both the trace and the proof file to `target/instruments/`.
Run `prove` before `verify` for each strategy.

| Target | Description |
|--------|-------------|
| `make profile-prove-age-rc` | Profile age prove (range check) |
| `make profile-verify-age-rc` | Profile age verify (range check) |

```bash
make profile-prove-age-rc
make profile-verify-age-rc
```

Traces are saved to `target/instruments/` and opened automatically in Instruments.app.
