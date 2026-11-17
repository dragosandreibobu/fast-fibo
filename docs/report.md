# FMSE — Homework H24: Verified Fast Fibonacci

**Language:** Dafny 4.11.0
**Scope:** Functional correctness, logarithmic recursion-step bound, signed-64-bit safety
**Source:** `src/FastFibonacci.dfy` and `src/Int64Fibonacci.dfy`

## A. Introduction

The Fibonacci sequence satisfies F(0)=0, F(1)=1 and F(n)=F(n-1)+F(n-2) for n>=2. The naive recursive evaluation redundantly recalculates subproblems. The fast-doubling method obtains F(2k) and F(2k+1) directly from F(k) and F(k+1), yielding logarithmic recursive depth.

This work establishes three machine-checked properties: (i) functional correctness for all natural indices, (ii) a precise upper and lower bound on recursive steps, and (iii) signed-64-bit representability of the specialized computation on its maximal safe input domain.

## B. Specifications

All mathematical indices have Dafny type `nat` (nonnegative integers). The reference sequence is modeled using unbounded `int` values, so correctness here does not silently assume fixed-width arithmetic. Dafny checks postconditions on **all** inputs satisfying their preconditions, rather than only on sampled examples.

### Level 1 — Functional correctness

- **S1 — Mathematical reference:** `Fib(0)=0`, `Fib(1)=1`, and for `n>=2`, `Fib(n)=Fib(n-1)+Fib(n-2)`. The recursive `function Fib(n: nat): int` terminates using `decreases n` and serves as a specification independent of the fast algorithm.
- **S2 — Even doubling:** for every `k: nat`, `Fib(2*k) == Fib(k)*(2*Fib(k+1)-Fib(k))`.
- **S3 — Odd doubling:** for every `k: nat`, `Fib(2*k+1) == Fib(k)*Fib(k)+Fib(k+1)*Fib(k+1)`.
- **S4 — Pair postconditions:** `FastPair(n)` ensures `x==Fib(n)` and `y==Fib(n+1)` (as well as a count specified in S7).
- **S5 — Public result postcondition:** `FastFib(n)` ensures `result==Fib(n)` for every `n: nat`, including zero.
- **S6 — Recursive termination:** `Doubling(k)` decreases its natural-number induction argument, and `FastPair(n)` recurses only on `n/2<n` when `n>0`.

**Supporting mathematical theorem:** `Addition(m,n)` proves, without any preconditions beyond `m,n: nat`,

```text
Fib(m+n+1) = Fib(m+1)*Fib(n+1) + Fib(m)*Fib(n).
```

The independent `DoublingFromAddition(k)` lemma establishes S2 and S3 from this formula. The original inductive `Doubling(k)` lemma is retained and remains the one invoked by `FastPair`. This provides two proof routes to the same algorithmic identities, without defining the reference sequence in terms of the fast algorithm.

### Level 2 — Logarithmic recursion-step complexity

- **S7 — Instrumented step count:** `FastPair(n)` ensures `steps==RecursiveSteps(n)`, with `RecursiveSteps(0)=0` and `RecursiveSteps(n)=1+RecursiveSteps(n/2)` for `n>0`.
- **S8 — Sign and base case:** `RecursiveSteps(0)==0` and `RecursiveSteps(n)>0` for `n>0`.
- **S9 — Lower power bound:** for `n>0`, `Pow2(steps-1)<=n`.
- **S10 — Upper power bound:** for `n>0`, `n<Pow2(steps)`.

`FastFibWithSteps(n)` combines S5 and S7–S10 in its postconditions. The two power bounds uniquely characterize the bit length `floor(log2(n))+1` for `n>0`. The counted quantity is non-base-case recursive calls, **not** CPU time or arbitrary-precision multiplication cost.

### Level 3 — Signed-64-bit representability (optional extension)

The `I64` refinement type restricts mathematical integers to `MIN64 <= x <= MAX64`, where `MIN64=-2^63` and `MAX64=2^63-1`.

- **S11 — Range of explicitly modeled intermediates:** each intermediate assigned to `I64` in the bounded implementations has a verified signed-64-bit range.
- **S12 — Pair precondition and result:** `FastPair64(n)` requires `n<=91` and ensures `x==Fib(n)` and `y==Fib(n+1)`.
- **S13 — Result-only precondition and result:** `FastFib64(n)` requires `n<=92` and ensures `result==Fib(n)`.
- **S14 — Exact boundary:** `Fib(92)=7540113804746346429 <= MAX64` and `Fib(93)=12200160415121876738 > MAX64`.
- **S15 — Maximal result domain:** for `n<=92`, `0<=Fib(n)<=MAX64`; for `n>=93`, `Fib(n)>MAX64`.
- **S16 — Maximal pair domain:** for `n<=91`, `0<=Fib(n+1)<=MAX64`; for `n>=92`, `Fib(n+1)>MAX64`.

The input type `nat` and the bounded-method preconditions are part of these contracts. The refinement checks do **not** amount to a proof about an unchecked hardware or compiler integer implementation.

## C. Encoding and proofs

### C.1 Independent reference and mathematical identities (Dragoș)

`Fib` is a transparent recursive mathematical *specification*, not the implementation of the fast algorithm. Its recurrence fixes the meaning of the postconditions; the implementation calls `FastPair`, not `Fib`, to calculate the result. The proof is therefore not circular.

The new `Addition(m,n)` lemma establishes the general addition identity by induction on `m`. At `m=0`, it reduces to `Fib(n+1)=Fib(n+1)`. At `m=1`, it reduces to the defining recurrence `Fib(n+2)=Fib(n+1)+Fib(n)`. For `m>=2`, the two induction hypotheses are:

```text
Fib(m+n)   = Fib(m)*Fib(n+1)   + Fib(m-1)*Fib(n)
Fib(m+n-1) = Fib(m-1)*Fib(n+1) + Fib(m-2)*Fib(n)
```

Adding both and applying the recurrence at `m+n+1`, `m+1`, and `m` yields:

```text
Fib(m+n+1) = Fib(m+1)*Fib(n+1) + Fib(m)*Fib(n).
```

Both fast-doubling identities follow by substitution, now proved in `DoublingFromAddition`:

- Set `m=n=k` to obtain `Fib(2*k+1)=Fib(k+1)^2+Fib(k)^2`.
- For `k>0`, set `m=k, n=k-1` to obtain `Fib(2*k)=Fib(k)*(Fib(k+1)+Fib(k-1))`, then use `Fib(k+1)=Fib(k)+Fib(k-1)` to rewrite the factor as `2*Fib(k+1)-Fib(k)`. Check `k=0` separately.

The pre-existing `Doubling(k)` lemma is intentionally retained as a second proof: induction on `k`, with `a=Fib(k-1)`, `b=Fib(k)`, `c=a+b=Fib(k+1)`. The induction hypotheses give `Fib(2*k-2)=a*(2*b-a)` and `Fib(2*k-1)=a*a+b*b`. The recurrence and Dafny `calc` blocks establish:

```text
Fib(2*k)   = (a*a+b*b)+a*(2*b-a) = b*(2*c-b)
Fib(2*k+1) = Fib(2*k)+Fib(2*k-1) = b*b+c*c
```

The addition lemma broadens the mathematical theory; neither the reference specification nor the original doubling proof has been replaced by an unverified assertion.

### C.2 Recursive implementation and termination (Dragoș)

For `n=0`, `FastPair` returns `(0,1,0)`, matching `(Fib(0),Fib(1),RecursiveSteps(0))`. For `n>0`, set `k=n/2` (integer division) and recursively obtain `a=Fib(k)` and `b=Fib(k+1)` by the induction hypothesis. Applying `Doubling(k)` produces:

```text
even = a*(2*b-a) = Fib(2*k)
odd  = a*a+b*b   = Fib(2*k+1)
```

If `n=2*k`, return `(even,odd)`. If `n=2*k+1`, return `(odd,even+odd)`; the recurrence establishes `even+odd=Fib(2*k+2)`. Therefore both returned components satisfy S4. The wrapper `FastFib` exposes the first component and inherits S5.

Termination is established by the well-founded natural-number measure `decreases n`. For every `n>0`, `0<=n/2<n`. The mathematical specification, the two lemma inductions and the recursive implementation each declare a decreasing measure; no depth cutoff or bounded testing hypothesis is used.

### C.3 The step counter and the proof's scope (Dragoș)

The same recursive call returns `childSteps`; the enclosing call sets `steps=childSteps+1`. This is compared with the independently defined `RecursiveSteps` recurrence. `DepthBounds` performs induction on `n` and proves `Pow2(steps-1)<=n<Pow2(steps)` for positive `n`, with `n=0` handled separately. Because `FastFibWithSteps` invokes `DepthBounds`, its output carries an exact bit-length certificate.

This is a bound on the number of fast-doubling recursive calls, not a machine instruction or bit-operation complexity bound. Values are arbitrary-precision integers; their arithmetic cost is not constant when the index grows.

### C.4 Signed-64-bit refinement (Dragoș; optional Level 3)

The separate `Int64Fibonacci` module imports the Level 1–2 model and adds the refinement type `I64`. Its supporting lemmas show nonnegativity, monotonicity and exact boundary values by recurrence plus doubling. Assignments to `I64` prove the range of the explicitly modeled expressions `2*b`, `2*b-a`, the even product, the individual odd squares, their sum, and the next-value addition.

`FastPair64` must restrict `n<=91` because its second result is `Fib(n+1)`. `FastFib64` can extend to `n=92` by computing a smaller pair and only the even formula, avoiding construction of `Fib(93)`. These results concern mathematical representability; a separately verified machine-integer implementation would be needed for a compiler-level claim.

### C.5 Iterative method (Iasmina; integration pending)

The iterative `src/IterativeFibonacci.dfy` implementation, its processed-bit invariants, and its termination argument belong to issues #2–#3. They must be integrated here only after the relevant source and independent verifier results are available. The existing recursive claims above do not imply that an as-yet-unmerged iterative algorithm is verified.

## D. Results

Verify the independent Level 1–2 source and the Level 3 source (which includes the former):

```sh
dafny verify src/FastFibonacci.dfy
dafny verify src/Int64Fibonacci.dfy
```

The original Level 1–2 implementation (before adding `Addition` and `DoublingFromAddition`) was reported as **12 verified, 0 errors**; the original Level 3 source was reported as **15 verified, 0 errors**. These counts refer to the earlier implementation and are not final results for the present branch.

**Evidence note — 17 November 2026 (recursive contribution only):** [GitHub Actions run 44076070769](https://github.com/dragosandreibobu/fast-fibo/actions/runs/44076070769) verified the source in draft PR #7 with Dafny 4.11.0. The CI logs show **16 verified, 0 errors** for `src/FastFibonacci.dfy` and **15 verified, 0 errors** for `src/Int64Fibonacci.dfy` (including the former file). These are verifier-reported verification-condition aggregate counts, not the number of individual theorems, test cases, or benchmarks.

**Final results for the combined recursive + iterative solution are pending.** Issue #5 owns the final verification matrix, elapsed times, failures (if any), and assumptions disclosure after the iterative source is integrated. Do not sum the two verification counts as if they were disjoint.

The project uses no `assume` or `{:axiom}` in the verification source. The mathematical correctness and representability properties above are mechanically verified. GitHub Actions is configured to run both verification commands on `main`.

The verified scope is functional correctness, an exact recursion-step bound, and safety of the explicitly modeled signed-64-bit intermediate results. Compiler-level or runtime performance claims are not made.

## E. Discussion

The central benefit of fast doubling is that a pair of consecutive Fibonacci values lets one recursive call calculate two new consecutive values. This makes the algorithm concise while still requiring a substantive inductive proof.

Counting steps in the algorithm itself avoids proving a bound only for an unrelated abstract recurrence. The two-sided power bound proves logarithmic recursion depth without involving floating-point logarithms.

Level 3 exposes an important API-design distinction: the pair-producing implementation needs n<=91 because F(93) cannot be its second output for n=92, while the result-only implementation can still compute F(92) safely. The proof therefore needs a special branch that does not generate F(93).

**Limitations:** the signed-64-bit proof operates on mathematical integers with a refinement type, not directly on a compiled hardware integer implementation. The analysis does not include an unchecked wrapping model, CPU instruction costs, compiler translations, memory usage, or general bit-complexity. The complete proof details are in `docs/complexity.md` and `docs/safety.md`.

### Discussion draft — proof engineering decisions (for joint review)

**Why return a pair?** The mathematical identities for `Fib(2*k)` and `Fib(2*k+1)` both depend on `Fib(k)` and `Fib(k+1)`. Returning the consecutive pair makes the inductive hypothesis strong enough for either parity of `n` without performing two independent recursive calculations. The result-only API then projects the first component. This is a deliberate instance of strengthening an invariant/interface to simplify a proof.

**Why keep two doubling proofs?** The direct induction in `Doubling(k)` follows the recurrence locally and shows how an elementary algebraic identity supports an algorithm. The new `Addition(m,n)` lemma is a reusable general theorem; `DoublingFromAddition(k)` demonstrates that both doubling formulas are special cases. This proof redundancy is not required for H24, but it helps audit whether fast doubling depends on any circular assumption. Both routes are verified against the same independently defined Fibonacci sequence.

**What is and is not proved?** Universal functional correctness and termination are established for all `nat` inputs using unbounded mathematical integers. Exact logarithmic *recursive-step count* is established separately. The signed-64-bit model certifies representability of designated arithmetic intermediates for bounded input domains, but it does not establish compiled machine-code safety under arbitrary language semantics. In particular, the recursive-step theorem must not be presented as a full bit-complexity or wall-clock runtime bound.

**Integration risk:** The iterative extension will require a new loop invariant encoding the processed index/bits and a termination measure for its loop. The successful recursive proof does not discharge either iterative obligation. Final claims, report Section D, and the shared discussion should distinguish the separately verified implementations and list the commands and verifier outputs for the exact submitted commit.

**Submission checklist for the joint review:** confirm that the teacher's H24 grading requirements are represented by S1–S16; ensure the final code contains no trust-bypassing `assume` or `{:axiom}` constructs; rerun CI on the merged final commit; document any limitations or incomplete iterative proof rather than treating unverified material as a result. The optional Level 2–3 extensions should remain identifiable as extensions, not implicit prerequisites for the Level 1 proof.
