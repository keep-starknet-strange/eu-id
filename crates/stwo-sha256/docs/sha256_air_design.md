# SHA-256 AIR Design

## Pseudocode

```text
// Scheduling
for i from 16 to 63
        s0 := (w[i-15] >>>  7) ^ (w[i-15] >>> 18) ^ (w[i-15] >>  3)
        s1 := (w[i-2] >>> 17) ^ (w[i-2] >>> 19) ^ (w[i-2] >> 10)
        w[i] := w[i-16] + s0 + w[i-7] + s1

// Round
for i from 0 to 63
        S1 := (e >>> 6) ^ (e >>> 11) ^ (e >>> 25)
        ch := (e and f) ^ ((~ e) & g)
        temp1 := h + S1 + ch + k[i] + w[i]
        S0 := (a >>> 2) ^ (a >>> 13) ^ (a >>> 22)
        maj := (a & b) ^ (a & c) ^ (b & c)
        temp2 := S0 + maj

        h := g
        g := f
        f := e
        e := d + temp1
        d := c
        c := b
        b := a
        a := temp1 + temp2
```

## Design for M31

### Round

Represent each word as low 16bit, high 16 bit.
Let `P(A,B,C)` be a bitwise operation.
Focus on: `P(a,b,c)`, `(a>>>2)^(a>>>13)^(a>>>22)`

1. Split `a.l,b.l,c.l` to 3 parts, by bit indices:
   `L0= 0 1 7 8 9 10 11`, `L1= 2 3 4 5 6`, `L2= 12 13 14 15`

   Split `a.h,b.h,c.h` to 3 parts, by bit indices:
   `H0= 18 19 20 21 22`, `H1= 28 29 30 31`, `H2=16 17 23 24 25 26 27`

   **Note:** Each part is stored unpacked. That is, it is just the input
   masked (AND) with the bit mask.

   Do not range check yet.

   **Cost:** `6*2T = 18T`

2. Each `a,b,c`, is now split to 6 parts, each of at most 7 bits.
   Use `<=21bit` lookup tables to compute `P(a,b,c)`, in 6 parts.
   These lookups also range check the parts, to make step 1 sound.

   **Cost:** `6T+6L`

3. For the function `(a>>>2)^(a>>>13)^(a>>>22)`, the following 11 output bits:
   `O0=[0, 1, 9, 10, 11, 12, 20, 21, 22, 23, 31]`
   Are only a function of the 16 input bits `L0 || H0 || H1`

   Similarly, the following 11 output bits:
   `O1=[4, 5, 6, 7, 15, 16, 17, 25, 26, 27, 28]`
   Are only a function of other 16 input bits `L1 || L2 || H2`

   The other 10 output bits are affected by both
   `O2=[2, 3, 8, 13, 14, 18, 19, 24]`

   We do a lookup from `L0 || H0 || H1` to `O0.L, O0.H, O2`, and a lookup
   from `L1 || L2 || H2` to `O1.L, O1.H, O2’`

   **Cost:** `6T + 2L`

4. We now need to XOR `O2` and `O2’`. We use a lookup from `O2, O2’` to
   `Res.L, Res.H`

   **Cost:** `2T + L`

   Now, we need to add ~ 7 numbers, each already split to L and H.

   **Cost:** `2T + 4L`

**Overall cost for half a round:** `34T+13L`
64 rounds, and assuming `L=2T`, we get ~ 7680 cells.

### How to find this nice set of bit indices

Look at `(a>>>2)^(a>>>13)^(a>>>22)`. Represent as rotate 2 followed by
`(a>>>0)^(a>>>11)^(a>>>20)`
Every output bit i is affected by `i-0`, `i-11`, `i-20`.

Take the indices: `{(a*11+b*20)%2**32 : 0<=a,b<4}`.
These are 16 indices. Moreover, when `a,b>=1`, the indices
`i-0, i-11, i-20` are all in the chosen set. So, we get 9 indices that
are only affected from within the set, for free. The 2 extra were
random. So, we got 11 good indices.

### Scheduling

In a very similar fashion.

1. Split `w[i-15]` to 4 parts

   **Cost:** `2T`

2. Lookups to `O0,O2` and `O1,O2’`

   **Cost:** `6T+2L`

3. XOR

   **Cost:** `2T+L`

4. Do that again for `w[i-2]`

5. Add

   **Cost:** `2T+4L`

**Scheduling Overall:** `2016`

---

**All in all:** `9696`
