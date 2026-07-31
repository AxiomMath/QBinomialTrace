import Mathlib
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

We work with ordinary formal power series in `ℚ[[q]]` (only integer exponents of
`q` occur in every object defined below).  The task formalizes several
statements about the *integer trace* series `𝒯_{r,k}` attached to the
`q`-binomial `[ (r+k) ; k ]_q = (q^{r+1};q)_k / (q;q)_k`, and the Han–Xiong
"1/2"-conjecture.

## Main Definitions

* Def 1: the Gaussian (`q`-)binomial coefficient `qbinom(k,s)` as a polynomial in
  `ℤ[q]` (`0` for `s > k`), with `β_{k,s}(n) := [q^n] qbinom(k,s)`.
* Def 2: `p_k(n)` = number of partitions of `n` into parts each `≤ k`
  (the coefficients of `1/(q;q)_k`).
* Def 3: exponent `E(s,r) := s(s+1)/2 + r·s`, integer support
  `S_{r,k} := { s ∈ {0,…,k} : E(s,r) ∈ ℤ }`, and the integer-trace coefficient
  `c_{r,k}(d) := ∑_{s ∈ S_{r,k}} (-1)^s ∑_{n≥0} β_{k,s}(n)·p_k(d - n - E(s,r))`.
* Def 4: the integer trace `𝒯_{r,k}(q) := ∑_{d≥0} c_{r,k}(d) q^d` and the
  coefficientwise partial order `F ⪰_q G :⟺ [q^n](F-G) ≥ 0 ∀ n`.
* Def 5: for `x ∈ ℚ_{>0}`, `den(x)` is the (positive) reduced denominator, and
  the even core `r♭ := 1 / lcm(den(r), 2)`.
* Def 6: `HX(k) :⟺ ∀ r ∈ ℚ_{>0}, 𝒯_{1/2,k} ⪰_q 𝒯_{r,k}` and `HX :⟺ ∀ k ≥ 1, HX(k)`.

## Main Statements

* Statement 1 (support dominance).
* Statement 2 (half-line dominance).
* Statement 3 (canonical reduction): 3(a) core dominance, 3(b) equivalence with
  the unit family `1/(2m)`, 3(c) finite check for fixed `k`.

Background source: `main.tex` and the Han–Xiong–Guo–Niu paper (exponent formula
eq. (6),(7), partition series eq. (12), convolution formula eq. (13),
even core eq. (14), conjecture eq. (8)).
-/

open Polynomial

/-! ## Main Definition(s) -/

/-- Definition 1.  The Gaussian (`q`-)binomial coefficient `qbinom(k,s)` as a
polynomial in `ℤ[q]`.  It is defined by the `q`-Pascal recursion
`[k+1 choose s+1]_q = [k choose s]_q + q^{s+1} · [k choose s+1]_q`, together with
`qbinom(k,0) = 1` and `qbinom(0,s+1) = 0`.  In particular `qbinom(k,s) = 0`
whenever `s > k` (see `qbinom_eq_zero_of_lt`).  For `0 ≤ s ≤ k` this agrees with
`(q;q)_k / ((q;q)_s · (q;q)_{k-s})` (see `qbinom_mul_qqPochhammer`). -/
noncomputable def qbinom : ℕ → ℕ → Polynomial ℤ
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (k + 1), (s + 1) => qbinom k s + (X : Polynomial ℤ) ^ (s + 1) * qbinom k (s + 1)
termination_by k s => (k, s)

/-- The `q`-Pochhammer symbol `(q;q)_n = ∏_{j=0}^{n-1} (1 - q^{j+1})` as a
polynomial in `ℤ[q]`. -/
noncomputable def qqPochhammer (n : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range n, (1 - (X : Polynomial ℤ) ^ (i + 1))

/-- `β_{k,s}(n) := [q^n] qbinom(k,s)`, the coefficient of `q^n` in the Gaussian
binomial coefficient. -/
noncomputable def betaCoeff (k s n : ℕ) : ℤ := (qbinom k s).coeff n

/-- Definition 2.  `p_k(n)` = number of partitions of `n` into parts each `≤ k`,
with `p_k(0) = 1`. -/
noncomputable def partCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => ∀ x ∈ p.parts, x ≤ k)).card

/-- Extension of `p_k` to integer arguments, taking the value `0` at negative
arguments (matching `p_k(n) = 0` for `n < 0`). -/
noncomputable def partCountZ (k : ℕ) (m : ℤ) : ℤ :=
  if 0 ≤ m then (partCount k m.toNat : ℤ) else 0

/-- Definition 3.  The exponent `E(s,r) := s(s+1)/2 + r·s ∈ ℚ`. -/
def exponent (s : ℕ) (r : ℚ) : ℚ := (s * (s + 1) / 2 : ℚ) + r * s

/-- Definition 3.  The integer support `S_{r,k} := { s ∈ {0,…,k} : E(s,r) ∈ ℤ }`.
Membership `E(s,r) ∈ ℤ` is expressed as `(E(s,r)).den = 1`. -/
noncomputable def support (r : ℚ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun s => (exponent s r).den = 1)

/-- For `s ∈ S_{r,k}` the rational `E(s,r)` is an integer; `exponentInt s r` is
that integer (obtained as the numerator, which equals `E(s,r)` when its
denominator is `1`). -/
def exponentInt (s : ℕ) (r : ℚ) : ℤ := (exponent s r).num

/-- Definition 3.  The integer-trace coefficient
`c_{r,k}(d) := ∑_{s ∈ S_{r,k}} (-1)^s ∑_{n≥0} β_{k,s}(n)·p_k(d - n - E(s,r))`.
The inner sum ranges over `n ∈ {0,…,d}`, which captures all nonvanishing terms
since `β_{k,s}(n) = 0` for `n < 0` and `p_k(d - n - E(s,r)) = 0` once
`n > d - E(s,r)` (recall `E(s,r) ≥ 0`). -/
noncomputable def cCoeff (r : ℚ) (k d : ℕ) : ℤ :=
  ∑ s ∈ support r k, (-1) ^ s *
    ∑ n ∈ Finset.range (d + 1),
      betaCoeff k s n * partCountZ k ((d : ℤ) - n - exponentInt s r)

/-- Definition 4.  The integer trace `𝒯_{r,k}(q) := ∑_{d≥0} c_{r,k}(d) q^d`
as a formal power series in `ℚ[[q]]`. -/
noncomputable def trace (r : ℚ) (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun d => (cCoeff r k d : ℚ))

/-- Definition 4.  The coefficientwise partial order on `ℚ[[q]]`:
`coeffLE F G` means `F ⪰_q G`, i.e. `[q^n](F - G) ≥ 0` for every `n ∈ ℕ`. -/
def coeffLE (F G : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, 0 ≤ PowerSeries.coeff (R := ℚ) n (F - G)

@[inherit_doc] infix:50 " ⪰q " => coeffLE

/-- Definition 5.  The even core of `r ∈ ℚ_{>0}`: `r♭ := 1 / lcm(den(r), 2)`.
Here `den(r) = r.den` is the reduced (positive) denominator of `r`. -/
def evenCore (r : ℚ) : ℚ := (1 : ℚ) / (Nat.lcm r.den 2 : ℚ)

/-- Definition 6.  The per-`k` Han–Xiong "1/2"-property:
`HX(k) :⟺ ∀ r ∈ ℚ_{>0}, 𝒯_{1/2,k} ⪰_q 𝒯_{r,k}`. -/
def HXk (k : ℕ) : Prop := ∀ r : ℚ, 0 < r → trace (1 / 2) k ⪰q trace r k

/-- Definition 6.  The Han–Xiong "1/2"-conjecture:
`HX :⟺ ∀ k ∈ ℤ_{>0}, HX(k)`. -/
def HX : Prop := ∀ k : ℕ, 1 ≤ k → HXk k

/-- The unit-family property for fixed `k`:
`UF(k) :⟺ ∀ m ∈ ℤ_{>0}, 𝒯_{1/2,k} ⪰_q 𝒯_{1/(2m),k}`. -/
def UFk (k : ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → trace (1 / 2) k ⪰q trace (1 / (2 * m)) k

/-! ### Correctness statements for the definitions

Since `qbinom` is defined by a recursion rather than directly as the Pochhammer
quotient, we record its characterizing properties. -/

/-- `qbinom(k,s) = 0` whenever `s > k`. -/
theorem qbinom_eq_zero_of_lt (k s : ℕ) (h : k < s) : qbinom k s = 0 := by
  sorry

/-- The Gaussian binomial identity: for `s ≤ k`,
`qbinom(k,s) · (q;q)_s · (q;q)_{k-s} = (q;q)_k`. -/
theorem qbinom_mul_qqPochhammer (k s : ℕ) (h : s ≤ k) :
    qbinom k s * (qqPochhammer s * qqPochhammer (k - s)) = qqPochhammer k := by
  sorry

/-- Def 2 correctness: the generating function of `p_k` is `1/(q;q)_k`, i.e.
`(q;q)_k · ∑_n p_k(n) q^n = 1` in `ℚ[[q]]`.  Here `(q;q)_k` is mapped into
`ℚ[[q]]` via the coercion of its integer coefficients. -/
theorem partCount_gen (k : ℕ) :
    (PowerSeries.mk (fun n => ((qqPochhammer k).coeff n : ℚ)))
      * PowerSeries.mk (fun n => (partCount k n : ℚ)) = 1 := by
  sorry

/-! ## Main Statement(s) -/

/-- Statement 1 (Theorem `thm:support-dominance`: Support dominance).
Let `u` and `r` be positive rationals (automatically in lowest terms as
elements of `ℚ`), with `d := den(u)` and `b := den(r)`.  Suppose
(i) `d` is even, (ii) `d ∣ lcm(b,2)`, (iii) `u ≤ r`.  Then for every integer
`k ≥ 1`, `𝒯_{u,k}(q) ⪰_q 𝒯_{r,k}(q)`. -/
theorem support_dominance (u r : ℚ) (hu : 0 < u) (hr : 0 < r)
    (hd_even : Even u.den) (hd_dvd : u.den ∣ Nat.lcm r.den 2) (hur : u ≤ r) :
    ∀ k : ℕ, 1 ≤ k → trace u k ⪰q trace r k := by
  sorry

/-- Statement 2 (Corollary `cor:half-line`: Half-line dominance).
For every rational `r` with `r ≥ 1/2` and every integer `k ≥ 1`,
`𝒯_{1/2,k}(q) ⪰_q 𝒯_{r,k}(q)`. -/
theorem half_line_dominance (r : ℚ) (hr : (1 : ℚ) / 2 ≤ r) :
    ∀ k : ℕ, 1 ≤ k → trace (1 / 2) k ⪰q trace r k := by
  sorry

/-- Statement 3(a) (Theorem `thm:canonical-reduction`, core dominance,
source `eq:core-dominates`).  For every positive rational `r` and every integer
`k ≥ 1`, `𝒯_{r♭,k}(q) ⪰_q 𝒯_{r,k}(q)`, where `r♭` is the even core of `r`. -/
theorem core_dominance (r : ℚ) (hr : 0 < r) :
    ∀ k : ℕ, 1 ≤ k → trace (evenCore r) k ⪰q trace r k := by
  sorry

/-- Statement 3(b) (Theorem `thm:canonical-reduction`, equivalence with the unit
family, source `eq:unit-family`).  The Han–Xiong conjecture `HX` holds iff the
`1/(2m)` unit family holds for all `k` and all `m ≥ 1`. -/
theorem HX_iff_unit_family :
    HX ↔ (∀ k : ℕ, 1 ≤ k → UFk k) := by
  sorry

/-- Statement 3(b), per-`k` equivalence: for every fixed integer `k ≥ 1`,
`HX(k) ⟺ UF(k)`. -/
theorem HXk_iff_UFk (k : ℕ) (hk : 1 ≤ k) : HXk k ↔ UFk k := by
  sorry

/-- Statement 3(c) (Theorem `thm:canonical-reduction`, finite check for fixed
`k`, source `eq:finite-unit-family`).  For every fixed integer `k ≥ 1`, if
`𝒯_{1/2,k}(q) ⪰_q 𝒯_{1/(2m),k}(q)` for every integer `m` with `2 ≤ m ≤ ⌊k/2⌋`,
then `HX(k)` holds.  (When `⌊k/2⌋ < 2`, i.e. `k ≤ 3`, the hypothesis is vacuous
and `HX(k)` holds unconditionally.) -/
theorem finite_unit_family_check (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ m : ℕ, 2 ≤ m → m ≤ k / 2 → trace (1 / 2) k ⪰q trace (1 / (2 * m)) k) :
    HXk k := by
  sorry
