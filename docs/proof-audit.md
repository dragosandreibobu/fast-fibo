# Recursive fast-Fibonacci proof audit — H24

**Reviewer:** Dragoș-Andrei Bobu  
**Target:** `src/FastFibonacci.dfy` (with bounded-arithmetic context from `src/Int64Fibonacci.dfy`)  
**Dafny:** 4.11.0  
**Related issues:** #1, #4, #6  
**Verification evidence:** [PR #7, first successful run](https://github.com/dragosandreibobu/fast-fibo/actions/runs/44075605811) (source commit `684ec246b9b9d3a1765c0372cf6582f9fdec38e4`)

## Verification evidence and method

The referenced GitHub Actions job ran exactly these commands, using Dafny 4.11.0, on the PR's proof-bearing source commit:

```sh
dafny verify src/FastFibonacci.dfy
dafny verify src/Int64Fibonacci.dfy
```

The job succeeded. The logs record **16 verified, 0 errors** for `FastFibonacci.dfy` and **15 verified, 0 errors** for `Int64Fibonacci.dfy`. These are *verifier-reported counts*, not counts of named lemmas and not evidence of execution benchmarks. The later report-only commits do not change the proof-bearing source.

## Contract-by-contract findings

| Declaration | Contract / verification obligation | Audit finding |
|---|---|---|
| `Fib(n)` | Mathematical reference for all `n:nat`; `decreases n` | Uses the original two-term recurrence. It does **not** define Fibonacci using fast doubling. |
| `Addition(m,n)` | `F(m+n+1)=F(m+1)F(n+1)+F(m)F(n)` | Induction on `m`. Both predecessor cases are invoked for `m>=2`; base cases `m=0,1` are explicit. No `assume`. |
| `DoublingFromAddition(k)` | Both even/odd doubling identities | Independent route from the addition lemma, including `k=0`; does not invoke the existing `Doubling` lemma. |
| `Doubling(k)` | Both identities for all `k:nat` | Existing induction on `k` remains intact. Recurrence and arithmetic are joined in explicit `calc` blocks. |
| `FastPair(n)` | `x=F(n)`, `y=F(n+1)`, `steps=RecursiveSteps(n)` | Base `n=0`; one recursive call for `n>0`; parity case split with `n=2k` or `n=2k+1`. Its implementation invokes the proved `Doubling(k)` identity. |
| `FastFib(n)` | `result=F(n)` | Thin wrapper over the first value returned by `FastPair`; no hidden stronger precondition. |
| `RecursiveSteps(n)` | Defined recurrence for counted non-base-case recursive calls | Mirrors `FastPair`'s actual step increments, rather than postulating an unrelated runtime function. |
| `DepthBounds(n)` | For `n>0`, `2^(S(n)-1)<=n<2^S(n)` | Structural induction on halved input; proof at `n=0,1` treated separately. |
| `FastFibWithSteps(n)` | Result, exact returned count, and the power bounds | Returns results from the instrumented method and invokes `DepthBounds`. |

### Non-circularity

The main proof dependencies run from the mathematical recurrence (`Fib`) to `Doubling`, to the recursive implementation's postconditions. The new general addition lemma is separately derived from `Fib` and yields a second proof of the doubling formulas; neither lemma assumes correctness of `FastPair` or `FastFib`. `FastFib` delegates to an already specified and verified pair-producing method.

### Termination

For positive `n:nat`, the recursive input `k=n/2` satisfies `k<n`; the code asserts this before its recursive call. `Doubling` and `Addition` decrease their respective natural-number induction arguments, and the recursive reference `Fib` decreases its index. Termination follows from well-founded decreases obligations, not a manually imposed bound on `n`.

### Scope / trust boundary

- The source contains no `assume` statements and no `{:axiom}` declarations. The proof relies on Dafny's mathematical-integer semantics, ordinary recursive-function reasoning, and SMT-backed arithmetic.
- It proves correctness for **every mathematical natural index**, but it does not prove that an actual fixed-width executable computing `Fib(n)` will avoid overflow at arbitrary `n`.
- The step counter proves recursive *call count* (specifically, non-base-case calls), not exact processor time, total bit operations, allocation cost, or `O(log n)` full machine-level runtime.
- `Int64Fibonacci.dfy` proves representability of explicitly modeled intermediates using a refinement of mathematical integers. This is a separate bounded implementation and not a compiler- or machine-code semantics theorem.
- An additional iterative proof is **not** established by this audit. Issues #2–#3 own its implementation and loop invariants, and issue #5 owns the consolidated report results.

## Reproduction

```sh
dafny verify src/FastFibonacci.dfy
dafny verify src/Int64Fibonacci.dfy
```

The CI workflow uses `dafny-lang/setup-dafny-action@v1` pinned to Dafny 4.11.0. Verifier counts may change when source files and declared proof obligations change. Record per-commit results rather than carrying old counts forward into the final report.

## Final-report integration

Sections **B** and **C.1–C.4** of `docs/report.md` describe the reviewed specifications, proofs, and model. Section **C.5** is deliberately reserved for the collaborator's iterative work. The jointly edited Section **E** should discuss proof-engineering tradeoffs and the limitations above. Section **D** must be refreshed from final merged verification runs by the assigned collaborator.
