# FMSE — Homework H24: Verified Fast Fibonacci

**Language:** Dafny 4.11.0
**Scope:** Functional correctness (recursive and iterative), logarithmic recursion-step bound, signed-64-bit safety
**Source:** `src/FastFibonacci.dfy`, `src/Int64Fibonacci.dfy`, and `src/IterativeFibonacci.dfy`

## A. Introduction

**Informal problem and input/output.** Given an index `n: nat` (a nonnegative integer), compute the nth Fibonacci number efficiently. The input domain includes `n=0`; the output is a mathematical integer `result` with `result = F(n)`, where `F(0)=0`, `F(1)=1`, and `F(n)=F(n-1)+F(n-2)` for `n>=2`. The central requirement of H24 is agreement with this *independent recursive reference specification*, not agreement with sampled test vectors. The desired properties are universal correctness, termination, and fast-doubling structure; additional results include an exact recursion-step bound and a bounded signed-64-bit interface. The iterative version is a team extension.

The naive recursive evaluation redundantly recalculates subproblems. The fast-doubling method obtains F(2k) and F(2k+1) directly from F(k) and F(k+1), yielding logarithmic recursive depth.

This work implements and formally verifies both a **recursive** and an **iterative (bit-based)** version of fast-doubling Fibonacci in Dafny, establishing four machine-checked properties: (i) functional correctness of the recursive implementation against the mathematical recurrence, (ii) a precise logarithmic bound on recursive steps, (iii) functional correctness and termination of the imperative iterative implementation via loop invariants, and (iv) signed-64-bit representability on the maximal safe input domain.

## B. Specifications

All mathematical indices have Dafny type `nat` (nonnegative integers). The reference sequence is modeled using unbounded `int` values, so correctness here does not silently assume fixed-width arithmetic. Dafny checks postconditions on **all** inputs satisfying their preconditions, rather than only on sampled examples.

**Formal correspondence.** The input type `nat` encodes the nonnegative-index precondition. S1 supplies the independent reference, S2–S3 the proved mathematical identities, S4–S5 the required postconditions, and S6 termination. S7–S10 certify a recursion-step model of efficiency; S11–S16 add a safe bounded-arithmetic variant. S17–S21 below capture the iterative correctness, loop invariants, and termination. Unlike array search, H24 has no index-bounds or membership property to specify.

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

### Level 4 — Iterative bit-based implementation and loop invariants

- **S17 — Iterative pair correctness:** `FastIterativePair(n)` returns `a = Fib(n)` and `b = Fib(n + 1)` for every natural number `n >= 0`, so both parity branches have the information needed for the next bit.
- **S18 — Iterative public correctness:** `FastIterativeFib(n)` returns `result = Fib(n)` for every `n >= 0`, which directly matches the H24 requirement.
- **S19 — Phase 1 loop invariant & termination:** In the bit-length discovery loop, `mask == Pow2(bits)` and `mask >= 1` hold on every iteration, providing the initial prefix and protecting the halving step; `decreases n + 1 - mask` establishes termination with `n < mask`.
- **S20 — Phase 2 bit-prefix loop invariant:** In the main MSB-to-LSB loop, `0 <= i <= bits`, `mask >= 1`, `mask == Pow2(i)`, `a == Fib(n / mask)`, and `b == Fib(n / mask + 1)` hold before and after every iteration; these properties bridge the processed bit-prefix to the desired final postcondition.
- **S21 — Phase 2 termination:** The strictly decreasing natural variant `decreases i` guarantees loop termination at `i == 0` (`mask == 1`, `n / mask == n`), turning the loop invariant into the output postcondition.

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

### C.5 Iterative bit-based encoding and loop invariants (Iasmina)

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
| `src/FastFibonacci.dfy` | Levels 1–2: Recursive fast doubling + $O(\log n)$ step bounds | 16 verified, 0 errors | 42.93 s* |
| `src/Int64Fibonacci.dfy` | Level 3: Signed 64-bit overflow safety (`n <= 92`) | 15 verified, 0 errors | 2.94 s |
| `src/IterativeFibonacci.dfy` | Level 4: Iterative bit-based fast doubling + loop invariants + `Main` | 12 verified, 0 errors | 2.22 s |

**Verification difficulty (resolved):** During integration, `Addition(m,n)` timed out at the default 30-second SMT limit on Windows (`15 verified, 0 errors, 1 time out`). Raising that lemma's verification limit to 120 seconds allowed the proof to complete (`16 verified, 0 errors`) without `assume`, `{:axiom}`, or any weakened specification. There are no remaining failed verification obligations in the final source.

The implementation is complete for the stated H24 properties. The optional general-addition lemma is given a 120-second SMT verification budget for cross-platform reliability; no proof steps are assumed. The source contains no `assume` or `{:axiom}`; final verification counts for the merged proof branch must be updated from a fresh run. GitHub Actions is configured to run verification of all three sources on `main`.

Running `dafny run src/IterativeFibonacci.dfy` confirms concrete execution on boundary and representative inputs:

```text
F(0)   = 0
F(1)   = 1
F(2)   = 1
F(100) = 354224848179261915075
```

*The first time is from an independently measured Windows run of the merged recursive source using a 120-second verifier limit; the other two file times are the previously reported reference measurements, and their verification counts were reconfirmed on the combined source. Wall-clock measurements depend on hardware and solver environment.*

**Scope & limitations:** The verified scope covers functional correctness of both implementations, an exact recursion-step bound, and safety of the explicitly modeled signed-64-bit intermediate results. Because the iterative implementation uses Dafny's arbitrary-precision `nat` and `int` types, it guarantees mathematical correctness without overflow for all `n >= 0`, rather than proving compiler-level code generation, fixed-width hardware bounds, or runtime performance claims.

## E. Discussion

### What was easy

The informal behavior and reference recurrence were straightforward to express with `n: nat` and the recursive function `Fib`. The pair-returning API also maps naturally to the two fast-doubling identities and provides a clear public postcondition `result == Fib(n)`.

### What was hard, and what we changed


### Difficulties encountered and their resolution

**Proving the doubling identities.** The fast-doubling formulas do not follow automatically from the Fibonacci recurrence in the verifier. The recursive proof uses the `Doubling` lemma, induction, and explicit algebraic calculation steps to connect `Fib(k)`, `Fib(k+1)`, `Fib(2k)`, and `Fib(2k+1)`. The executable recursive implementation then reuses the lemma rather than assuming the identities.

**Relating the iterative state to the input.** Unlike the recursive implementation, the iterative version requires a loop invariant expressing what has already been processed. The key invariant is `(a,b) = (Fib(n / mask), Fib(n / mask + 1))`, with `mask = Pow2(i)`. It describes the processed binary prefix and is maintained by the even/odd fast-doubling update. A separate invariant `mask = Pow2(bits)` establishes the initial bit-length, while decreasing variants justify termination of both loops.

**Arithmetic reasoning during bit extraction.** Connecting successive prefixes requires `(n / m) / 2 = n / (2*m)` for positive `m`. This is not merely an algebraic rewrite for an SMT solver reasoning about integer division. The implementation introduces `DivMul2`, supported by `DivSmall`, `DivStep`, and `MulCancelDiv`, with explicit induction and Euclidean-division reasoning to make the proof tractable.

**Proving the exact recursion-step bound.** A separate asymptotic claim would not establish the cost of the implemented method. The recursive implementation therefore returns an instrumented step count and proves it equals `RecursiveSteps(n)`. The `DepthBounds` lemma establishes `2^(steps-1) <= n < 2^steps` for positive `n`, yielding an exact bit-length characterization.

**Avoiding signed-64-bit overflow.** The pair-returning interface must produce `F(n+1)` as well as `F(n)`, so its maximum input is 91, whereas the result-only interface can accept 92. The latter uses a special branch for 92 that avoids constructing `F(93)`. Intermediate values are checked against the `I64` refinement type; this is a representability proof over mathematical integers, not a proof about a particular compiled binary.

### What we did not accomplish

We did not verify a fixed-width compiled machine executable, a wall-clock running-time bound, memory use, or bit-complexity for arbitrary-precision arithmetic. `decreases` proves termination; the separate `RecursiveSteps` model establishes the exact number of non-base recursive calls, which is narrower than machine-level runtime.

### Interesting findings and trade-offs

The general `Addition(m,n)` lemma gives a second, independently structured proof of both doubling formulas, helping audit the absence of circularity. The recursive version closely follows mathematical induction and needs no loop invariants. The iterative version eliminates recursive calls in its algorithmic structure but requires a more involved state invariant and division lemmas. Both use the same verified mathematical doubling identities. The exact recursion-step theorem counts pair calculations under a unit-cost arithmetic model, not bit-operation runtime. Likewise, the arbitrary-precision iterative result is correct for every natural input, while the signed-64-bit implementation needs a bounded domain.

### Verification evidence and limitations

With Dafny 4.11.0, the three source files were independently checked on 19 November 2026: `FastFibonacci.dfy` (16 verified, 0 errors), `Int64Fibonacci.dfy` (15 verified, 0 errors), and `IterativeFibonacci.dfy` (12 verified, 0 errors). The iterative executable also produced `F(0)=0`, `F(1)=1`, `F(2)=1`, and `F(100)=354224848179261915075`, and exited successfully. These verification counts are per invocation and may include checks of included dependencies; they should not be interpreted as 43 distinct specifications.

