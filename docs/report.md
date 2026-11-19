# FMSE — Homework H24: Verified Fast Fibonacci

**Language:** Dafny 4.11.0
**Scope:** Functional correctness (recursive and iterative), logarithmic recursion-step bound, signed-64-bit safety
**Source:** `src/FastFibonacci.dfy`, `src/Int64Fibonacci.dfy`, and `src/IterativeFibonacci.dfy`

## A. Introduction

The Fibonacci sequence satisfies F(0)=0, F(1)=1 and F(n)=F(n-1)+F(n-2) for n>=2. The naive recursive evaluation redundantly recalculates subproblems. The fast-doubling method obtains F(2k) and F(2k+1) directly from F(k) and F(k+1), yielding logarithmic recursive depth.

This work implements and formally verifies both a **recursive** and an **iterative (bit-based)** version of fast-doubling Fibonacci in Dafny, establishing four machine-checked properties: (i) functional correctness of the recursive implementation against the mathematical recurrence, (ii) a precise logarithmic bound on recursive steps, (iii) functional correctness and termination of the imperative iterative implementation via loop invariants, and (iv) signed-64-bit representability on the maximal safe input domain.

## B. Specifications

### Level 1 — Functional correctness

- **S1 — Reference sequence:** `Fib(n)` represents the standard recurrence for all n>=0.
- **S2 — Even doubling:** F(2k)=F(k)*(2*F(k+1)-F(k)).
- **S3 — Odd doubling:** F(2k+1)=F(k)^2+F(k+1)^2.
- **S4 — Pair correctness:** `FastPair(n)` returns x=F(n), y=F(n+1).
- **S5 — Public correctness:** `FastFib(n)` returns F(n).
- **S6 — Termination:** the natural-number recursive measure strictly decreases in every non-base-case call.

### Level 2 — Logarithmic recursion-step complexity

- **S7 — Step counting:** `FastPair(n)` returns `steps=RecursiveSteps(n)`, where S(0)=0 and S(n)=1+S(floor(n/2)) for n>0.
- **S8 — Nonnegative/positive count:** S(0)=0 and S(n)>0 for n>0.
- **S9 — Lower bound:** for n>0, `Pow2(steps-1)<=n`.
- **S10 — Upper bound:** for n>0, `n<Pow2(steps)`.

S9–S10 establish an exact binary bit-length bound, implying S(n)=floor(log2(n))+1 for n>0. The method `FastFibWithSteps` publishes the verified result/count pair.

### Level 3 — Signed-64-bit representability

Define the refinement type `I64` by `-2^63 <= x <= 2^63-1`.

- **S11 — Intermediate safety:** every explicitly computed intermediate in `FastPair64` and `FastFib64` is assigned only after proving its value belongs to `I64`.
- **S12 — Bounded pair correctness:** for 0<=n<=91, `FastPair64(n)` returns a representable pair (F(n), F(n+1)).
- **S13 — Bounded result correctness:** for 0<=n<=92, `FastFib64(n)` returns a representable F(n).
- **S14 — Exact boundary:** `Fib(92)=7540113804746346429 <= MAX64` but `Fib(93)=12200160415121876738 > MAX64`.
- **S15 — Maximal result domain:** for n<=92, 0<=F(n)<=MAX64; for n>=93, F(n)>MAX64.
- **S16 — Maximal pair domain:** for n<=91, F(n+1) fits; for n>=92, F(n+1)>MAX64.

The Level 3 preconditions restrict inputs to these proven safe domains. None of the proofs treats signed integers as silently wrapping modulo 2^64.

### Level 4 — Iterative bit-based implementation and loop invariants

- **S17 — Iterative pair correctness:** `FastIterativePair(n)` returns `a = Fib(n)` and `b = Fib(n + 1)` for every natural number `n >= 0`.
- **S18 — Iterative public correctness:** `FastIterativeFib(n)` returns `result = Fib(n)` for every `n >= 0`.
- **S19 — Phase 1 loop invariant & termination:** In the bit-length discovery loop, `mask == Pow2(bits)` and `mask >= 1` hold on every iteration, and `decreases n + 1 - mask` proves termination with `n < mask`.
- **S20 — Phase 2 bit-prefix loop invariant:** In the main MSB-to-LSB loop, `0 <= i <= bits`, `mask >= 1`, `mask == Pow2(i)`, `a == Fib(n / mask)`, and `b == Fib(n / mask + 1)` hold before and after every iteration.
- **S21 — Phase 2 termination:** The strictly decreasing natural variant `decreases i` guarantees loop termination at `i == 0` (`mask == 1`, `n / mask == n`).

## C. Encoding and proofs

### Mathematical model and doubling lemma

The Dafny function `Fib` is an independent reference specification; the executable fast-doubling method never calls it to compute the answer.

`Doubling(k)` proves the identities simultaneously by induction. For k>0 let a=F(k-1), b=F(k), c=F(k+1)=a+b. The inductive hypotheses are:

```text
F(2k-2)=a*(2b-a)
F(2k-1)=a*a+b*b
```

The recurrence gives:

```text
F(2k)=F(2k-1)+F(2k-2)
     =a*a+b*b+a*(2b-a)
     =b*(2(a+b)-b)=b*(2c-b).

F(2k+1)=F(2k)+F(2k-1)=b*b+c*c.
```

These equations are expressed using `calc` blocks and explicit recursive lemma calls. The executable `FastPair` makes one recursive call on k=floor(n/2); even and odd cases reconstruct the required pair. The `decreases` contracts prove termination.

### Logarithmic recursion bound

The same `FastPair` implementation counts its non-base-case recursive calls. A separate function `RecursiveSteps` defines the counting recurrence and the method proves its returned count equals that specification. The lemma `DepthBounds` proves the two-sided powers-of-two bound by induction on n.

For k=floor(n/2)>0, suppose d=RecursiveSteps(k) and `2^(d-1)<=k<2^d`. Since `2k<=n<2(k+1)` and `RecursiveSteps(n)=d+1`, doubling yields `2^d<=n<2^(d+1)`. The base cases n=0 and n=1 are verified separately.

### Signed-64-bit range safety

`Int64Fibonacci` imports `FastFibonacci`. It defines a subset type `I64` with inclusive bounds MIN64 and MAX64. The specialized algorithm proves the range for `2*b`, `2*b-a`, the even product, the two odd squares and their sum, and the addition used to form F(n+1). Assigning each to `I64` introduces a range obligation checked by Dafny.

To avoid expanding the Fibonacci recurrence at n=93 directly, `BoundaryValues` proves values up to F(24) by recurrence and applies the already proved `Doubling` lemma at 23 and 46. This gives exact values for F(46), F(47), F(92), and F(93).

The `FibNonnegative`, `FibMonotone`, and `FibOrder` lemmas prove bounds on all earlier Fibonacci values. Together with the exact boundary they establish the maximum safe domains for `FastPair64` and `FastFib64`. The latter handles n=92 separately, computing F(92) but not F(93).

### Iterative bit-based encoding and loop invariants

`IterativeFibonacci` imports `FastFibonacci` and reuses `Fib`, `Pow2`, and `Doubling` without duplicating the inductive proof. Rather than using fixed-width bitvectors (`bv64`), which would restrict inputs to `n < 2^64`, the iterative method operates on unbounded `nat` values and extracts bits arithmetically via integer division by powers of two.

1. **Finding the bit-length (Phase 1):** A first loop doubles `mask` (starting from `1`) while `mask <= n`, maintaining `mask == Pow2(bits)`. Upon exit, `n < mask`, meaning `n / mask == 0` is the empty bit-prefix of `n`.
2. **Processing bits from MSB to LSB (Phase 2):** A second loop decrements `i` from `bits` down to `0`, halving `mask` at each step (`nextMask = mask / 2 = Pow2(i - 1)`). The core invariant states that `(a, b)` always equals `(Fib(n / mask), Fib(n / mask + 1))`, where `n / mask` is the integer formed by the already-processed most-significant bits of `n`.
3. **Connecting division to doubling:** The helper lemma `DivMul2` (supported by linear induction lemmas `DivSmall`, `MulCancelDiv`, and `DivStep` to avoid nonlinear Z3 solver timeouts) proves `(n / nextMask) / 2 == n / (2 * nextMask) == n / mask`. Consequently, the new bit-prefix `q = n / nextMask` satisfies `q = 2 * prefix + bit`, where `bit = q % 2`. Calling `Doubling(prefix)` yields `Fib(2 * prefix)` and `Fib(2 * prefix + 1)`, and the conditional branch updates `(a, b)` for `bit == 0` or `bit == 1`. When `i` reaches `0`, `mask == Pow2(0) == 1`, so `n / mask == n` and `a == Fib(n)`.

## D. Results

Verify the independent Level 1–2 source, the Level 3 signed-64-bit source, and the Level 4 iterative bit-based source using **Dafny 4.11.0** (`4.11.0+fcb2042d6d`):

```sh
dafny verify src/FastFibonacci.dfy
dafny verify src/Int64Fibonacci.dfy
dafny verify src/IterativeFibonacci.dfy
```

| Source file | Scope | Verification result | Time |
| :--- | :--- | :--- | ---: |
| `src/FastFibonacci.dfy` | Levels 1–2: Recursive fast doubling + $O(\log n)$ step bounds | 12 verified, 0 errors | 3.70 s |
| `src/Int64Fibonacci.dfy` | Level 3: Signed 64-bit overflow safety (`n <= 92`) | 15 verified, 0 errors | 2.94 s |
| `src/IterativeFibonacci.dfy` | Level 4: Iterative bit-based fast doubling + loop invariants + `Main` | 12 verified, 0 errors | 2.22 s |

All specifications (**S1–S21**) were completely proved, with zero failed specifications in the final version. The codebase is complete and uses **no `assume` or `{:axiom}`** in the verification source. GitHub Actions is configured to run verification on `main`.

Running `dafny run src/IterativeFibonacci.dfy` confirms concrete execution on boundary and representative inputs:

```text
F(0)   = 0
F(1)   = 1
F(2)   = 1
F(100) = 354224848179261915075
```

**Scope & limitations:** The verified scope covers functional correctness of both implementations, an exact recursion-step bound, and safety of the explicitly modeled signed-64-bit intermediate results. Because the iterative implementation uses Dafny's arbitrary-precision `nat` and `int` types, it guarantees mathematical correctness without overflow for all `n >= 0`, rather than proving compiler-level code generation, fixed-width hardware bounds, or runtime performance claims.

## E. Discussion

The central benefit of fast doubling is that a pair of consecutive Fibonacci values lets one recursive call calculate two new consecutive values. This makes the algorithm concise while still requiring a substantive inductive proof.

Counting steps in the algorithm itself avoids proving a bound only for an unrelated abstract recurrence. The two-sided power bound proves logarithmic recursion depth without involving floating-point logarithms.

Level 3 exposes an important API-design distinction: the pair-producing implementation needs n<=91 because F(93) cannot be its second output for n=92, while the result-only implementation can still compute F(92) safely. The proof therefore needs a special branch that does not generate F(93).

**Limitations:** the signed-64-bit proof operates on mathematical integers with a refinement type, not directly on a compiled hardware integer implementation. The analysis does not include an unchecked wrapping model, CPU instruction costs, compiler translations, memory usage, or general bit-complexity. The complete proof details are in `docs/complexity.md` and `docs/safety.md`.

**Recursive vs. iterative verification trade-offs:** Implementing both versions highlighted a key contrast in deductive verification. The recursive method (`FastPair`) mirrors the mathematical induction directly and requires no loop invariants, whereas the iterative method (`FastIterativePair`) avoids recursion overhead at runtime but requires expressing the partially processed binary prefix `n / Pow2(i)` as an explicit loop invariant and decomposing Euclidean division (`DivMul2` via `MulCancelDiv` and `DivStep`) into linear inductive steps so Z3 can verify it without timing out.