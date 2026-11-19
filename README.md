# Verified Fast Fibonacci — FMSE Homework H24

This repository implements the **fast-doubling Fibonacci algorithm** and formally verifies four complementary properties in Dafny 4.11.0:

1. **Level 1 — Functional correctness and termination** for every natural-number input.
2. **Level 2 — Exact logarithmic recursion depth**, certified by an instrumented step counter.
3. **Level 3 — Signed-64-bit overflow safety**, with the maximal safe input range established mathematically.
4. **Level 4 — Iterative bit-based fast doubling**, with verified loop invariants and termination.

## Run the proofs

Install [Dafny 4.11.0](https://dafny.org/latest/Installation) and execute:

```sh
dafny verify src/FastFibonacci.dfy
dafny verify src/Int64Fibonacci.dfy
dafny verify src/IterativeFibonacci.dfy
```

All three files are verified by [GitHub Actions](.github/workflows/verify.yml) on pushes to `main` and pull requests.

## Level 1: algorithm correctness

`FastFibonacci.dfy` defines an independent mathematical specification `Fib`:

```text
F(0)=0, F(1)=1, F(n)=F(n-1)+F(n-2).
```

The `Doubling` lemma proves:

```text
a=F(k), b=F(k+1)
F(2k)   = a*(2*b-a)
F(2k+1) = a*a+b*b
```

The implementation `FastPair(n)` returns `F(n)` and `F(n+1)` by recursion on `floor(n/2)`. The public method `FastFib(n)` returns the correct value of `F(n)` for all natural n.

The project additionally proves the general **Fibonacci addition formula** from the original recursive reference:

```text
F(m+n+1) = F(m+1)*F(n+1) + F(m)*F(n)
```

`Addition(m,n)` proves the identity by induction on `m`. `DoublingFromAddition(k)` then derives the two doubling identities algebraically without invoking the original `Doubling(k)` lemma. Keeping both the inductive and general-theorem derivations provides independently structured proof arguments for the same formulas; the executable algorithm continues using the original `Doubling` proof.

The contract-by-contract verification audit is available in [`docs/proof-audit.md`](docs/proof-audit.md).

## Level 2: exact logarithmic bound

`FastPair` also returns a count `steps` of non-base-case recursive calls. Dafny verifies that it matches an independent counting specification and, for n>0:

```text
2^(steps-1) <= n < 2^steps
```

Thus `steps = floor(log2(n))+1` for n>0; n=0 gives steps=0. This is a proof of **O(log n) recursion steps**, not a machine-level bit-operation runtime bound. `FastFibWithSteps(n)` exposes both value and certified count.

## Level 3: signed-64-bit representability

`Int64Fibonacci.dfy` defines the mathematical signed-64-bit range through a Dafny refinement type `I64`. All intermediate arithmetic results of the specialized algorithm are proven to fit in that range.

| Interface | Valid natural-number inputs | Correct result |
|---|---|---|
| `FastPair64(n)` | 0–91 | `(F(n), F(n+1))` |
| `FastFib64(n)` | 0–92 | `F(n)` |

The result-only interface handles n=92 without constructing the unrepresentable F(93). Dafny proves the exact boundary:

```text
F(92) = 7,540,113,804,746,346,429  (fits)
F(93) = 12,200,160,415,121,876,738 (does not fit)
signed 64-bit maximum = 9,223,372,036,854,775,807
```

A complete proof of representability is **not** the same as verifying a particular machine-code binary. The source uses mathematical integers with range-refinement proof obligations.

## Level 4: iterative fast doubling

`IterativeFibonacci.dfy` processes the binary digits of `n` from most significant to least significant. Dafny proves the loop invariants connecting the current pair to the processed prefix, termination of both loops, and the postcondition `result == Fib(n)` for every natural input. Run `dafny run src/IterativeFibonacci.dfy` for the concrete examples.

## Repository layout

- [`src/FastFibonacci.dfy`](src/FastFibonacci.dfy) — Levels 1 and 2
- [`src/Int64Fibonacci.dfy`](src/Int64Fibonacci.dfy) — Level 3, including the original module
- [`src/IterativeFibonacci.dfy`](src/IterativeFibonacci.dfy) — Level 4, iterative correctness and loop invariants
- [`docs/complexity.md`](docs/complexity.md) — logarithmic bound and proof explanation
- [`docs/safety.md`](docs/safety.md) — 64-bit model, exact boundaries, safe intermediate operations
- [`docs/report.md`](docs/report.md) — FMSE homework report (sections A–E)
- [`docs/proof-audit.md`](docs/proof-audit.md) — proof dependencies, contract audit, and verification evidence
- [`.github/workflows/verify.yml`](.github/workflows/verify.yml) — reproducible CI

**Scope:** nonnegative indices; mathematical integer semantics with range checks; no claims of fixed machine runtime or correctness of an unchecked overflowing executable.
