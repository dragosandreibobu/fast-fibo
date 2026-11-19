// FMSE H24: Iterative bit-based fast-doubling implementation,
// loop invariants, and termination proof.
include "FastFibonacci.dfy"

module IterativeFibonacci {
  import opened FastFibonacci

  // Helper lemma: powers of 2 are strictly positive.
  lemma Pow2Positive(e: nat)
    ensures Pow2(e) >= 1
    decreases e
  {
    if e > 0 {
      Pow2Positive(e - 1);
    }
  }

  // Helper lemma: dividing a smaller non-negative number yields 0.
  lemma DivSmall(a: nat, d: nat)
    requires 0 <= a < d
    ensures a / d == 0
  {}

  // Helper lemma: uniqueness of quotient in Euclidean division (linear induction).
  lemma MulCancelDiv(q1: nat, q2: nat, d: nat, r1: nat, r2: nat)
    requires d > 0
    requires 0 <= r1 < d && 0 <= r2 < d
    requires q1 * d + r1 == q2 * d + r2
    ensures q1 == q2
    decreases q1
  {
    if q1 == 0 {
      if q2 > 0 {
        assert q2 * d == (q2 - 1) * d + d;
        assert (q2 - 1) * d >= 0;
        assert false;
      }
    } else if q2 == 0 {
      assert q1 * d == (q1 - 1) * d + d;
      assert (q1 - 1) * d >= 0;
      assert false;
    } else {
      assert q1 * d == (q1 - 1) * d + d;
      assert q2 * d == (q2 - 1) * d + d;
      assert (q1 - 1) * d + r1 == (q2 - 1) * d + r2;
      MulCancelDiv(q1 - 1, q2 - 1, d, r1, r2);
    }
  }

  // Helper lemma: adding the divisor increments the quotient by 1.
  lemma DivStep(a: nat, d: nat)
    requires d > 0
    ensures (a + d) / d == a / d + 1
  {
    var q: nat := a / d;
    var r: nat := a % d;
    assert a == q * d + r;
    assert 0 <= r < d;

    var q1: nat := (a + d) / d;
    var r1: nat := (a + d) % d;
    assert a + d == q1 * d + r1;
    assert 0 <= r1 < d;

    assert (q + 1) * d == q * d + d;
    assert q1 * d + r1 == (q + 1) * d + r;
    MulCancelDiv(q1, q + 1, d, r1, r);
  }

  // Helper lemma: integer division by m followed by 2 equals division by 2*m.
  lemma DivMul2(n: nat, m: nat)
    requires m > 0
    ensures (n / m) / 2 == n / (2 * m)
    decreases n
  {
    var d: nat := 2 * m;
    assert d > 0;
    if n < m {
      DivSmall(n, m);
      DivSmall(n, d);
    } else if n < d {
      var a: nat := n - m;
      assert n == a + m;
      assert a < m;
      DivSmall(a, m);
      DivStep(a, m);
      assert n / m == 1;
      DivSmall(n, d);
    } else {
      var n2: nat := n - d;
      assert n == n2 + d;
      DivStep(n2, d);
      assert n / d == n2 / d + 1;

      assert n == (n2 + m) + m;
      DivStep(n2 + m, m);
      DivStep(n2, m);
      assert n / m == n2 / m + 2;

      DivStep(n2 / m, 2);
      assert (n / m) / 2 == (n2 / m) / 2 + 1;

      DivMul2(n2, m);
    }
  }

  // Iterative fast-doubling algorithm processing the binary representation
  // of n from the most significant bit to the least significant bit.
  method FastIterativePair(n: nat) returns (a: int, b: int)
    ensures a == Fib(n)
    ensures b == Fib(n + 1)
  {
    // Phase 1: Find the smallest power of 2 strictly greater than n.
    var bits: nat := 0;
    var mask: nat := 1;
    while mask <= n
      invariant mask >= 1
      invariant mask == Pow2(bits)
      decreases n + 1 - mask
    {
      bits := bits + 1;
      mask := mask * 2;
    }

    // At exit: mask == Pow2(bits) and n < mask, so the initial prefix n / mask is 0.
    assert mask == Pow2(bits);
    assert n < mask;
    assert n / mask == 0;

    // Phase 2: Process bits from MSB to LSB.
    var i: nat := bits;
    a := 0;
    b := 1;

    while i > 0
      invariant 0 <= i <= bits
      invariant mask >= 1
      invariant mask == Pow2(i)
      invariant a == Fib(n / mask)
      invariant b == Fib(n / mask + 1)
      decreases i
    {
      Pow2Positive(i - 1);
      var nextMask: nat := mask / 2;
      assert mask == Pow2(i) == 2 * Pow2(i - 1);
      assert nextMask == Pow2(i - 1);
      assert mask == 2 * nextMask;

      var prefix: nat := n / mask;
      DivMul2(n, nextMask);
      assert (n / nextMask) / 2 == prefix;

      var q: nat := n / nextMask;
      var bit: nat := q % 2;
      assert q == 2 * prefix + bit;

      // Apply the verified fast-doubling identities to advance from prefix to 2*prefix.
      Doubling(prefix);
      var c: int := a * (2 * b - a);
      var d: int := a * a + b * b;
      assert c == Fib(2 * prefix);
      assert d == Fib(2 * prefix + 1);

      if bit == 0 {
        assert q == 2 * prefix;
        a, b := c, d;
      } else {
        assert bit == 1;
        assert q == 2 * prefix + 1;
        assert Fib(2 * prefix + 2) == Fib(2 * prefix + 1) + Fib(2 * prefix);
        a, b := d, c + d;
      }

      mask := nextMask;
      i := i - 1;
    }

    // At exit: i == 0, so mask == Pow2(0) == 1 and n / mask == n.
    assert i == 0;
    assert mask == Pow2(0) == 1;
    assert n / mask == n;
  }

  // Public result-only iterative interface matching the H24 specification.
  method FastIterativeFib(n: nat) returns (result: int)
    ensures result == Fib(n)
  {
    var following: int;
    result, following := FastIterativePair(n);
  }

  // Verification checks and concrete execution on boundary and representative inputs.
  method Main()
  {
    var f0 := FastIterativeFib(0);
    var f1 := FastIterativeFib(1);
    var f2 := FastIterativeFib(2);
    var f100 := FastIterativeFib(100);
    var r100 := FastFib(100);

    assert f0 == 0;
    assert f1 == 1;
    assert f2 == 1;
    assert f100 == Fib(100);
    assert f100 == r100;

    print "F(0)   = ", f0, "\n";
    print "F(1)   = ", f1, "\n";
    print "F(2)   = ", f2, "\n";
    print "F(100) = ", f100, "\n";
  }
}
