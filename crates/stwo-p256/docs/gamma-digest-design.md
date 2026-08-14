# Gamma-digest range reshape

## Status

This document describes the active gamma-digest gadget in
`crates/stwo-p256/src/components/gamma_digest`.

The final-add and public-key curve components use this gadget. The source
defines the exact layouts, tags, and value order.

## Purpose

A wide P-256 row can contain many values that need range checks. One LogUp
fraction for each value gives the wide component a large interaction trace.

The gamma-digest gadget moves these range uses to a narrow, tall component.
The wide row emits one digest tuple for each range kind.

The transformation preserves this property:

```text
each value in the fixed wide-row list belongs to its assigned range table
```

## Challenge order

The channel draws `gamma` after the base-trace commitment. Thus, committed
values cannot depend on the digest challenge.

`GammaChallenge` stores `gamma` and its powers. It stores enough powers for
the largest padded value list.

## Wide-row digest

For a fixed value list of length `L`, let `P` be the next multiple of eight.
The digest is:

```text
D = sum(v[i] * gamma^(P - 1 - i))
```

Tail positions contain a fixed `pad_value`. That value must belong to the
assigned range table.

The wide-row relation tuple is:

```text
(tag, row_index, d0, d1, d2, d3)
```

The four digest coordinates are M31-linear expressions of existing base
columns. The wide component needs no new base columns or digest constraints.
It adds one negative relation entry with multiplicity `presence`.

## Tall layout

One `GammaTallInstance` serves one component and one range kind. Its static
layout contains:

- a unique tag
- the number of wide-row groups
- the number of values in each group

Each tall row contains eight values. `GAMMA_DIGEST_LANES` fixes this width.

The preprocessed columns are:

- `row_id`
- `start`
- `end`
- `in_group`

`row_id` identifies the source wide row. `start` and `end` identify the group
boundaries. `in_group` is one on all scheduled tall rows.

The base trace has eight value columns. Extra rows after the schedule contain
zeros.

## Accumulator

The interaction trace has four M31 accumulator coordinates. Together, they
represent one QM31 value.

For one tall row, the AIR checks:

```text
acc =
    (1 - start) * acc_previous * gamma^8
  + sum(value[j] * gamma^(7 - j))
```

This constraint has degree two. A start row removes the cyclic predecessor.
Padding rows continue the accumulator but emit no relation entries.

At a group end, `acc` equals the wide-row digest for that value sequence.

## Relation signs

The `GammaDigestRelation` has arity six:

```text
(tag, row_index, d0, d1, d2, d3)
```

The wide row supplies a negative digest term. The tall group end supplies the
matching positive term.

Each scheduled tall lane supplies one positive range-table use. The range
provider supplies the matching negative term.

The total LogUp balance is zero only when both conditions hold:

1. The tall values have the same digest as the wide values.
2. Each tall value belongs to its range table.

## Fixed schedule

The verifier reconstructs the preprocessed schedule from public component
shape data. The schedule must not depend on witness values.

Each active wide row has one digest group. Each scheduled tall lane has one
range use. A witness gate cannot omit a scheduled check.

The adopted value lists are fixed by their component layouts. Inactive formula
cells contain valid table values, such as zero or the encoded zero carry.

## Tags and row indexes

Each active component and range kind has a distinct tag. The row index also
forms part of the tuple.

A digest from another component, range kind, or row cannot cancel the expected
term unless it matches all tuple fields.

## Degree bounds

The wide digest coordinates have degree one in base trace values. The tall
accumulator recurrence has degree two.

Tall LogUp entries use preprocessed numerators. The implementation batches two
fractions in each LogUp column. The component uses
`max_constraint_log_degree_bound = log_size + 1`.

## Collision bound

Assume two different committed value sequences have the same digest. Their
difference defines a nonzero polynomial in `gamma`.

The maximum polynomial degree is less than the padded value count. A
Schwartz-Zippel bound limits the collision probability by:

```text
(P - 1) / |QM31|
```

The current value lists keep this term below the design budget of `2^-114`.
The global LogUp argument has its separate soundness bound.

## Active component values

The final-add component has two gamma groups:

- 13-limb range values
- signed carry values

The public-key curve component also has two groups:

- coordinate range values
- signed carry values

The component modules define the exact column lists. Do not duplicate those
lists in this document.

## Failure cases

Verification must fail for these changes:

- a changed tall value
- two tall rows in the wrong order
- a wrong component tag
- a wrong row index
- an out-of-range tall value
- a changed group boundary in a noncanonical preprocessed trace

The unit tests in `components/gamma_digest/mod.rs` cover value changes, row
swaps, tag mismatches, honest constraints, and balance.

## Security boundary

The gamma digest is a probabilistic equality check over committed values. It
does not hide those values.

The gadget reduces interaction width. It does not give proof-wide zero
knowledge or unlinkability.

## Source map

| Path | Purpose |
|---|---|
| `components/gamma_digest/mod.rs` | Shared digest and tall-component logic |
| `components/final_add/air.rs` | Final-add wide-row digest entries |
| `components/final_add/trace.rs` | Final-add tall traces |
| `components/public_key_curve/air.rs` | Public-key curve digest and tall traces |
| `proof/mod.rs` | Challenge and relation order |
