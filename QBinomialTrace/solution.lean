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

/-- Reflexivity of the coefficientwise order. -/
theorem coeffLE_refl (F : PowerSeries ℚ) : F ⪰q F := by
  intro n
  simp

/-- Transitivity of the coefficientwise order.  If `F ⪰q G` and `G ⪰q H` then
`F ⪰q H`, since `[q^n](F-H) = [q^n](F-G) + [q^n](G-H)` and each summand is
nonnegative. -/
theorem coeffLE_trans {F G H : PowerSeries ℚ} (h1 : F ⪰q G) (h2 : G ⪰q H) :
    F ⪰q H := by
  intro n
  have hFG := h1 n
  have hGH := h2 n
  have hsum : PowerSeries.coeff (R := ℚ) n (F - H)
      = PowerSeries.coeff (R := ℚ) n (F - G) + PowerSeries.coeff (R := ℚ) n (G - H) := by
    simp only [map_sub]; ring
  rw [hsum]
  linarith


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
  induction k generalizing s with
  | zero =>
    match s with
    | 0 => omega
    | s + 1 => simp [qbinom]
  | succ n ih =>
    match s with
    | 0 => omega
    | s + 1 =>
      simp only [qbinom]
      have h1 : n < s := by omega
      have h2 : n < s + 1 := by omega
      rw [ih s h1, ih (s + 1) h2]
      simp

/-- `qqPochhammer 0 = 1`. -/
theorem qqPochhammer_zero : qqPochhammer 0 = 1 := by
  simp [qqPochhammer]

/-- Recursion for `qqPochhammer`: `(q;q)_{n+1} = (q;q)_n · (1 - X^{n+1})`. -/
theorem qqPochhammer_succ (n : ℕ) :
    qqPochhammer (n + 1) = qqPochhammer n * (1 - (X : Polynomial ℤ) ^ (n + 1)) := by
  simp only [qqPochhammer, Finset.prod_range_succ]

/-- The diagonal value: `qbinom k k = 1`. -/
theorem qbinom_self (k : ℕ) : qbinom k k = 1 := by
  induction k with
  | zero => simp [qbinom]
  | succ n ih =>
    simp only [qbinom]
    rw [ih, qbinom_eq_zero_of_lt n (n + 1) (by omega)]
    ring

/-- The Gaussian binomial identity: for `s ≤ k`,
`qbinom(k,s) · (q;q)_s · (q;q)_{k-s} = (q;q)_k`. -/
theorem qbinom_mul_qqPochhammer (k s : ℕ) (h : s ≤ k) :
    qbinom k s * (qqPochhammer s * qqPochhammer (k - s)) = qqPochhammer k := by
  induction k generalizing s with
  | zero =>
    interval_cases s
    simp [qbinom, qqPochhammer_zero]
  | succ k ih =>
    match s with
    | 0 =>
      simp only [qbinom, Nat.sub_zero, qqPochhammer_zero, one_mul]
    | t + 1 =>
      -- s = t+1 ≤ k+1, so t ≤ k.
      have ht : t ≤ k := by omega
      rcases Nat.lt_or_ge t k with htk | htk
      · -- 1 ≤ s = t+1 ≤ k : main case, both IH at t and t+1 apply
        have ht1 : t + 1 ≤ k := by omega
        -- q-Pascal: qbinom (k+1)(t+1) = qbinom k t + X^(t+1) * qbinom k (t+1)
        -- index shifts
        have hsub1 : (k + 1) - (t + 1) = k - t := by omega
        have hkt_pos : 1 ≤ k - t := by omega
        have hsub2 : k - t = (k - (t + 1)) + 1 := by omega
        have hexp : (t + 1) + (k - t) = k + 1 := by omega
        -- IH at t: qbinom k t * (P_t * P_{k-t}) = P_k
        have IHt := ih t (by omega)
        -- IH at t+1: qbinom k (t+1) * (P_{t+1} * P_{k-(t+1)}) = P_k
        have IHt1 := ih (t + 1) ht1
        -- q-Pascal for qbinom (k+1)(t+1)
        have hpascal : qbinom (k + 1) (t + 1)
            = qbinom k t + (X : Polynomial ℤ) ^ (t + 1) * qbinom k (t + 1) := by
          simp only [qbinom]
        -- P_{t+1} = P_t * (1 - X^{t+1})
        have hPt1 := qqPochhammer_succ t
        -- P_{k-t} = P_{k-(t+1)} * (1 - X^{k-t})   (via hsub2)
        have hPkt : qqPochhammer (k - t)
            = qqPochhammer (k - (t + 1)) * (1 - (X : Polynomial ℤ) ^ (k - t)) := by
          conv_lhs => rw [hsub2]
          rw [qqPochhammer_succ]
          rw [show k - (t + 1) + 1 = k - t by omega]
        -- P_{k+1} = P_k * (1 - X^{k+1})
        have hPk1 := qqPochhammer_succ k
        -- exponent identity: X^(t+1) * X^(k-t) = X^(k+1)
        have hpow : (X : Polynomial ℤ) ^ (t + 1) * (X : Polynomial ℤ) ^ (k - t)
            = (X : Polynomial ℤ) ^ (k + 1) := by
          rw [← pow_add, hexp]
        -- Rewrite IH facts so their Pochhammer terms match the expanded goal.
        rw [hPkt] at IHt
        rw [hPt1] at IHt1
        rw [hsub1, hpascal, hPk1, hPt1]
        conv_lhs => rw [hPkt]
        -- Now close with a linear combination of the (rewritten) IH facts and hpow.
        linear_combination (1 - (X : Polynomial ℤ) ^ (t + 1)) * IHt
          + (X : Polynomial ℤ) ^ (t + 1) * (1 - (X : Polynomial ℤ) ^ (k - t)) * IHt1
          - qqPochhammer k * hpow
      · -- t = k, so s = k+1 (diagonal)
        have : t = k := by omega
        subst this
        -- qbinom (k+1)(k+1) = 1, P_{k+1-(k+1)} = P_0 = 1
        rw [qbinom_self]
        simp only [Nat.sub_self, qqPochhammer_zero, mul_one, one_mul]

/-- Power-series generating function of `qqPochhammer k` (coefficients cast ℤ→ℚ). -/
noncomputable def Pgen (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((qqPochhammer k).coeff n : ℚ))

/-- Power-series generating function of `partCount k`. -/
noncomputable def Qgen (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (partCount k n : ℚ))

/-- `Pgen 0 = 1`. -/
theorem Pgen_zero : Pgen 0 = 1 := by
  unfold Pgen
  rw [qqPochhammer_zero]
  ext n
  rw [PowerSeries.coeff_mk]
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [Polynomial.coeff_one]
  · simp [Polynomial.coeff_one, h, PowerSeries.coeff_one]

/-- `Qgen 0 = 1`: only the empty partition of `0` has all parts `≤ 0`. -/
theorem Qgen_zero : Qgen 0 = 1 := by
  unfold Qgen
  ext n
  rw [PowerSeries.coeff_mk]
  rcases eq_or_ne n 0 with h | h
  · subst h
    have : partCount 0 0 = 1 := by decide
    rw [this]
    simp [PowerSeries.coeff_one]
  · have hpc : partCount 0 n = 0 := by
      unfold partCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _
      push_neg
      have hsum : p.parts.sum = n := p.parts_sum
      by_contra hc
      push_neg at hc
      have hz : p.parts = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]
        intro x hx
        have hpos := p.parts_pos hx
        have := hc x hx
        omega
      rw [hz, Multiset.sum_zero] at hsum
      exact h hsum.symm
    rw [hpc]
    simp [PowerSeries.coeff_one, h]

/-- Product recurrence for `Pgen`: `Pgen (k+1) = Pgen k * (1 - X^(k+1))`. -/
theorem Pgen_succ (k : ℕ) :
    Pgen (k + 1) = Pgen k * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) := by
  -- phi : ℤ[X] →+* ℚ[[q]] mapping a polynomial to its power series with ℤ→ℚ cast.
  set phi : Polynomial ℤ →+* PowerSeries ℚ :=
    (PowerSeries.map (Int.castRingHom ℚ)).comp Polynomial.coeToPowerSeries.ringHom with hphi
  have hPgen : ∀ j : ℕ, Pgen j = phi (qqPochhammer j) := by
    intro j
    unfold Pgen
    ext n
    rw [PowerSeries.coeff_mk, hphi]
    simp only [RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_map,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, Int.coe_castRingHom,
      eq_intCast]
  rw [hPgen (k + 1), hPgen k, qqPochhammer_succ]
  rw [map_mul, map_sub, map_one, map_pow]
  congr 2
  -- phi X = PowerSeries.X
  rw [hphi]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, PowerSeries.map_X]

/-- Partition recurrence (`n < k+1` case): a partition of `n < k+1` cannot use a
part `= k+1`, so "parts `≤ k+1`" and "parts `≤ k`" cut out the same partitions. -/
theorem partCount_succ_of_lt (k n : ℕ) (h : n < k + 1) :
    partCount (k + 1) n = partCount k n := by
  unfold partCount
  congr 1
  apply Finset.filter_congr
  intro p _
  constructor
  · intro hp x hx
    -- each part x ≤ n (since positive and sum = n), and n ≤ k
    have hxle : x ≤ n := by
      have := Multiset.single_le_sum (fun y _ => Nat.zero_le y) x hx
      rw [p.parts_sum] at this
      exact this
    omega
  · intro hp x hx
    have := hp x hx
    omega

/-- Partition recurrence (`n ≥ k+1` case), stated with `n + (k+1)`:
`partCount (k+1) (n+(k+1)) = partCount k (n+(k+1)) + partCount (k+1) n`.
Class A = no part `= k+1` (⇔ all parts `≤ k`), Class B = at least one part
`= k+1`; removing one copy of `k+1` bijects Class B with partitions of `n` with
parts `≤ k+1`. -/
theorem partCount_recurrence (k n : ℕ) :
    partCount (k + 1) (n + (k + 1))
      = partCount k (n + (k + 1)) + partCount (k + 1) n := by
  -- Split partitions of N := n+(k+1) with parts ≤ k+1 by whether they contain
  -- a part = k+1.  Class A (no such part) ⇔ all parts ≤ k = partCount k N.
  -- Class B (some part = k+1) ⇔ remove one copy → bijection with partCount (k+1) n.
  set N := n + (k + 1) with hN
  -- The full filter set (all parts ≤ k+1).
  set S := Finset.univ.filter (fun p : Nat.Partition N => ∀ x ∈ p.parts, x ≤ k + 1) with hS
  -- Predicate: contains a part equal to k+1.
  -- Class A = partitions in S with no part = k+1; Class B = with a part = k+1.
  have hsplit :
      partCount (k + 1) N
        = (S.filter (fun p => ¬ (k + 1) ∈ p.parts)).card
          + (S.filter (fun p => (k + 1) ∈ p.parts)).card := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (p := fun p : Nat.Partition N => (k + 1) ∈ p.parts)
    rw [partCount, ← hS]
    omega
  rw [hsplit]
  congr 1
  · -- Class A = partCount k N
    rw [hS, Finset.filter_filter, partCount]
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hle, hnotin⟩ x hx
      have := hle x hx
      rcases Nat.lt_or_ge x (k + 1) with h' | h'
      · omega
      · exfalso; apply hnotin; have : x = k + 1 := by omega
        rwa [this] at hx
    · intro hle
      refine ⟨fun x hx => le_trans (hle x hx) (Nat.le_succ k), ?_⟩
      intro hin
      have := hle (k + 1) hin
      omega
  · -- Class B = partCount (k+1) n, via the bijection removing one copy of (k+1)
    rw [partCount]
    -- membership of p in the Class-B filter gives (k+1) ∈ p.parts
    have hBin : ∀ p : Nat.Partition N,
        p ∈ S.filter (fun p => (k + 1) ∈ p.parts) → (k + 1) ∈ p.parts := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact hp.2
    -- Forward map: remove one copy of (k+1).
    refine Finset.card_bij'
      (i := fun (p : Nat.Partition N) hp =>
        (⟨p.parts.erase (k + 1),
          fun {i} hi => p.parts_pos (Multiset.mem_of_mem_erase hi),
          by
            have hin : (k + 1) ∈ p.parts := hBin p hp
            have hsum : (k + 1) + (p.parts.erase (k + 1)).sum = p.parts.sum :=
              Multiset.sum_erase hin
            rw [p.parts_sum] at hsum
            omega⟩ : Nat.Partition n))
      (j := fun (σ : Nat.Partition n) _ =>
        (⟨(k + 1) ::ₘ σ.parts,
          fun {i} hi => by
            rcases Multiset.mem_cons.mp hi with rfl | hi'
            · omega
            · exact σ.parts_pos hi',
          by rw [Multiset.sum_cons, σ.parts_sum, hN]; omega⟩ : Nat.Partition N))
      ?_ ?_ ?_ ?_
    · -- forward image membership in target filter
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hpS := (Finset.mem_filter.mp hp).1
      rw [hS, Finset.mem_filter] at hpS
      intro x hx
      exact hpS.2 x (Multiset.mem_of_mem_erase hx)
    · -- backward image membership in S with (k+1) ∈ parts
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      refine ⟨?_, Multiset.mem_cons_self _ _⟩
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx'
      · exact le_refl _
      · exact hσ x hx'
    · -- left_inv: erase then cons back
      intro p hp
      apply Nat.Partition.ext
      simp only
      exact Multiset.cons_erase (hBin p hp)
    · -- right_inv: cons then erase
      intro σ hσ
      apply Nat.Partition.ext
      simp only
      exact Multiset.erase_cons_head _ _

/-- Generating-function recurrence for `Qgen`:
`(1 - X^(k+1)) * Qgen (k+1) = Qgen k`.  Equivalent to the partition recurrence
`partCount (k+1) n - partCount (k+1) (n-(k+1)) = partCount k n`. -/
theorem Qgen_succ (k : ℕ) :
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) * Qgen (k + 1) = Qgen k := by
  ext n
  rw [Qgen, Qgen]
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hn : k + 1 ≤ n
  · rw [if_pos hn]
    rw [PowerSeries.coeff_mk]
    -- use recurrence with m := n - (k+1), so n = m + (k+1)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
    rw [partCount_recurrence]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg hn, PowerSeries.coeff_mk]
    push_neg at hn
    rw [partCount_succ_of_lt k n hn, sub_zero]

/-- Def 2 correctness: the generating function of `p_k` is `1/(q;q)_k`, i.e.
`(q;q)_k · ∑_n p_k(n) q^n = 1` in `ℚ[[q]]`.  Here `(q;q)_k` is mapped into
`ℚ[[q]]` via the coercion of its integer coefficients. -/
theorem partCount_gen (k : ℕ) :
    (PowerSeries.mk (fun n => ((qqPochhammer k).coeff n : ℚ)))
      * PowerSeries.mk (fun n => (partCount k n : ℚ)) = 1 := by
  show Pgen k * Qgen k = 1
  induction k with
  | zero => rw [Pgen_zero, Qgen_zero, mul_one]
  | succ m ih =>
      rw [Pgen_succ]
      calc Pgen m * (1 - (PowerSeries.X : PowerSeries ℚ) ^ (m + 1)) * Qgen (m + 1)
          = Pgen m * ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (m + 1)) * Qgen (m + 1)) := by
            ring
        _ = Pgen m * Qgen m := by rw [Qgen_succ]
        _ = 1 := ih

/-! ## Nonnegativity helpers -/

/-- The Gaussian binomial coefficient has nonnegative integer coefficients. -/
theorem qbinom_coeff_nonneg (k s n : ℕ) : 0 ≤ (qbinom k s).coeff n := by
  induction k generalizing s n with
  | zero =>
    match s with
    | 0 => simp [qbinom, Polynomial.coeff_one]; split <;> norm_num
    | s + 1 => simp [qbinom]
  | succ k ih =>
    match s with
    | 0 => simp [qbinom, Polynomial.coeff_one]; split <;> norm_num
    | s + 1 =>
      simp only [qbinom, Polynomial.coeff_add]
      have h1 := ih s n
      have h2 : 0 ≤ ((X : Polynomial ℤ) ^ (s + 1) * qbinom k (s + 1)).coeff n := by
        rw [Polynomial.coeff_X_pow_mul']
        split
        · exact ih (s + 1) (n - (s + 1))
        · exact le_refl 0
      linarith

/-- `betaCoeff k s n ≥ 0`. -/
theorem betaCoeff_nonneg (k s n : ℕ) : 0 ≤ betaCoeff k s n :=
  qbinom_coeff_nonneg k s n

/-- `partCountZ k m ≥ 0`. -/
theorem partCountZ_nonneg (k : ℕ) (m : ℤ) : 0 ≤ partCountZ k m := by
  unfold partCountZ
  split
  · positivity
  · exact le_refl 0

/-! ## Support-dominance core: group by `s`, then extract `(1-q)` -/

/-- Support characterization: `E(s,ρ) ∈ ℤ ⟺ ρ.den ∣ s`. -/
theorem exponent_den_eq_one_iff (rho : ℚ) (hrho : 0 < rho) (s : ℕ) :
    (exponent s rho).den = 1 ↔ rho.den ∣ s := by
  -- Step 1: strip the triangular number s(s+1)/2, which is a natural cast.
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self s
  have hcast : (s * (s + 1) / 2 : ℚ) = (t : ℚ) := by
    have hh : (s * (s + 1) : ℚ) = ((2 * t : ℕ) : ℚ) := by
      exact_mod_cast (by omega : s * (s + 1) = 2 * t)
    rw [hh]; push_cast; ring
  have hexp : exponent s rho = (t : ℚ) + rho * s := by
    unfold exponent; rw [hcast]
  rw [hexp, Rat.natCast_add_den]
  -- Step 2: express rho * s as (a * s)/rho.den with a := rho.num.toNat.
  set a : ℕ := rho.num.toNat with ha
  have hnum_pos : 0 < rho.num := Rat.num_pos.mpr hrho
  have hacast : (a : ℚ) = (rho.num : ℚ) := by
    rw [ha]; exact_mod_cast Int.toNat_of_nonneg hnum_pos.le
  have hden_ne' : rho.den ≠ 0 := rho.den_ne_zero
  have hrewrite : rho * (s : ℚ) = ((a * s : ℕ) : ℚ) / ((rho.den : ℕ) : ℚ) := by
    have hden_pos : (0 : ℚ) < (rho.den : ℚ) := by exact_mod_cast rho.pos
    have hcast2 : ((a * s : ℕ) : ℚ) = (rho.num : ℚ) * (s : ℚ) := by
      push_cast; rw [hacast]
    have hmul : rho * (rho.den : ℚ) = (rho.num : ℚ) := Rat.mul_den_eq_num rho
    rw [hcast2, eq_div_iff hden_pos.ne']
    calc rho * (s : ℚ) * (rho.den : ℚ)
        = (rho * (rho.den : ℚ)) * (s : ℚ) := by ring
      _ = (rho.num : ℚ) * (s : ℚ) := by rw [hmul]
  rw [hrewrite]
  rw [Rat.den_div_natCast_eq_one_iff (a * s) rho.den hden_ne']
  -- coprimality: gcd(rho.den, a) = 1 since rho.num.natAbs coprime rho.den.
  have hcop : Nat.Coprime rho.den a := by
    have hna : rho.num.natAbs = a := by
      have h1 : (rho.num.natAbs : ℤ) = rho.num := Int.natAbs_of_nonneg hnum_pos.le
      have h2 : (a : ℤ) = rho.num := by rw [ha]; exact Int.toNat_of_nonneg hnum_pos.le
      omega
    rw [Nat.Coprime, Nat.gcd_comm, ← hna]
    exact rho.reduced
  exact hcop.dvd_mul_left

/-- `E(s,ρ) ≥ 0` for `ρ > 0`. -/
theorem exponentInt_nonneg (rho : ℚ) (hrho : 0 < rho) (s : ℕ) :
    0 ≤ exponentInt s rho := by
  unfold exponentInt
  rw [Rat.num_nonneg]
  unfold exponent
  have h1 : (0 : ℚ) ≤ (s * (s + 1) / 2 : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ rho * s := by positivity
  linarith

/-- The exponent as a natural number. -/
noncomputable def exponentNat (s : ℕ) (rho : ℚ) : ℕ := (exponentInt s rho).toNat

/-- `exponentNat` casts back to `exponentInt` when nonnegative. -/
theorem exponentNat_cast (rho : ℚ) (hrho : 0 < rho) (s : ℕ) :
    ((exponentNat s rho : ℤ)) = exponentInt s rho := by
  unfold exponentNat
  exact Int.toNat_of_nonneg (exponentInt_nonneg rho hrho s)

/-- The shifted `q`-binomial series `q^A · [k choose s]_q`. -/
noncomputable def qbinomShift (k s A : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if A ≤ n then ((qbinom k s).coeff (n - A) : ℚ) else 0

/-- `qbinomShift` has nonnegative coefficients. -/
theorem qbinomShift_nonneg (k s A n : ℕ) :
    0 ≤ PowerSeries.coeff (R := ℚ) n (qbinomShift k s A) := by
  unfold qbinomShift
  rw [PowerSeries.coeff_mk]
  split
  · exact_mod_cast qbinom_coeff_nonneg k s (n - A)
  · exact le_refl 0

/-- The `a`-th geometric series `1/(1-q^a) = ∑_m q^{am}`. -/
noncomputable def geom (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if a ∣ n then 1 else 0

theorem one_sub_Xpow_mul_geom (a : ℕ) (ha : 0 < a) :
    (1 - PowerSeries.X ^ a) * geom a = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  unfold geom
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hn : a ≤ n
  · rw [if_pos hn, PowerSeries.coeff_mk]
    by_cases hdvd : a ∣ n
    · -- a ∣ n and n ≥ a > 0, so n ≠ 0, and a ∣ n-a
      have hdvd2 : a ∣ n - a := Nat.dvd_sub hdvd (dvd_refl a)
      rw [if_pos hdvd, if_pos hdvd2, if_neg (by omega : n ≠ 0)]; ring
    · have han : a < n := by
        rcases lt_or_eq_of_le hn with h | h
        · exact h
        · exact absurd (h ▸ dvd_refl a) hdvd
      have hdvd2 : ¬ a ∣ n - a := by
        rw [Nat.dvd_sub_self_right]
        push_neg
        exact ⟨hdvd, han⟩
      rw [if_neg hdvd, if_neg hdvd2, if_neg (by rintro rfl; exact hdvd (dvd_zero a))]; ring
  · rw [if_neg hn]
    by_cases hne : n = 0
    · subst hne
      rw [if_pos (dvd_zero a), if_pos rfl]; ring
    · have hn0 : ¬ a ∣ n := fun hdvd => hn (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd)
      rw [if_neg hn0, if_neg hne]; ring

theorem geom_nonneg (a n : ℕ) : 0 ≤ PowerSeries.coeff (R := ℚ) n (geom a) := by
  unfold geom; rw [PowerSeries.coeff_mk]; split <;> norm_num

/-- The geometric series `1/(1-q) = ∑ q^n`. -/
noncomputable def geom1 : PowerSeries ℚ := PowerSeries.mk fun _ => 1

theorem geom1_nonneg (n : ℕ) : 0 ≤ PowerSeries.coeff (R := ℚ) n geom1 := by
  unfold geom1; rw [PowerSeries.coeff_mk]; norm_num

theorem one_sub_X_mul_geom1 : (1 - PowerSeries.X) * geom1 = 1 := by
  have h : geom1 = geom 1 := by
    unfold geom1 geom
    ext n; rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]; simp
  rw [h]
  have := one_sub_Xpow_mul_geom 1 (by norm_num)
  rwa [pow_one] at this

/-- The finite geometric series `∑_{A ≤ n < B} q^n = q^A(1-q^{B-A})/(1-q)`. -/
noncomputable def finiteGeom (A B : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if A ≤ n ∧ n < B then 1 else 0

theorem finiteGeom_nonneg (A B n : ℕ) :
    0 ≤ PowerSeries.coeff (R := ℚ) n (finiteGeom A B) := by
  unfold finiteGeom; rw [PowerSeries.coeff_mk]; split <;> norm_num

theorem one_sub_X_mul_finiteGeom {A B : ℕ} (hAB : A ≤ B) :
    (1 - PowerSeries.X) * finiteGeom A B = PowerSeries.X ^ A - PowerSeries.X ^ B := by
  ext n
  rw [sub_mul, one_mul, map_sub, map_sub]
  rw [PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  rw [show (PowerSeries.X : PowerSeries ℚ) * finiteGeom A B
      = PowerSeries.X ^ 1 * finiteGeom A B by rw [pow_one]]
  rw [PowerSeries.coeff_X_pow_mul']
  unfold finiteGeom
  simp only [PowerSeries.coeff_mk]
  by_cases h1 : 1 ≤ n
  · rw [if_pos h1]
    split_ifs <;>
      first
        | rfl
        | (exfalso; omega)
        | norm_num
  · rw [if_neg h1]
    split_ifs <;>
      first
        | rfl
        | (exfalso; omega)
        | norm_num

/-- Products of nonnegative-coefficient power series are nonnegative. -/
theorem mul_coeff_nonneg {F G : PowerSeries ℚ}
    (hF : ∀ n, 0 ≤ PowerSeries.coeff (R := ℚ) n F)
    (hG : ∀ n, 0 ≤ PowerSeries.coeff (R := ℚ) n G) :
    ∀ n, 0 ≤ PowerSeries.coeff (R := ℚ) n (F * G) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hF p.1) (hG p.2)

/-- The numerator series `N_{ρ,k} = ∑_{s ∈ S} (-1)^s q^{E(s,ρ)} [k choose s]_q`. -/
noncomputable def numTrace (rho : ℚ) (k : ℕ) : PowerSeries ℚ :=
  ∑ s ∈ support rho k,
    ((-1 : ℚ) ^ s) • qbinomShift k s (exponentNat s rho)

/-- Trace factorization: `𝒯_{ρ,k} = N_{ρ,k} · Q_k`. -/
theorem trace_eq_numTrace_mul_Qgen (rho : ℚ) (hrho : 0 < rho) (k : ℕ) :
    trace rho k = numTrace rho k * Qgen k := by
  -- Per-`s` key identity relating the inner convolution sum to a shifted product.
  have key : ∀ (s d : ℕ),
      ((∑ n ∈ Finset.range (d + 1),
          betaCoeff k s n * partCountZ k ((d : ℤ) - n - exponentInt s rho) : ℤ) : ℚ)
        = PowerSeries.coeff (R := ℚ) d
            (qbinomShift k s (exponentNat s rho) * Qgen k) := by
    intro s d
    set A : ℕ := exponentNat s rho with hA
    have hAcast : (A : ℤ) = exponentInt s rho := exponentNat_cast rho hrho s
    -- RHS via coeff_mul → range sum
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    -- Common target form for both sides.
    have hLHS :
        ((∑ n ∈ Finset.range (d + 1),
            betaCoeff k s n * partCountZ k ((d : ℤ) - n - exponentInt s rho) : ℤ) : ℚ)
          = ∑ n ∈ Finset.range (d + 1),
              (if n + A ≤ d then ((qbinom k s).coeff n : ℚ) * (partCount k (d - n - A) : ℚ)
               else 0) := by
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      unfold betaCoeff partCountZ
      rw [← hAcast]
      by_cases hle : n + A ≤ d
      · have h0 : (0 : ℤ) ≤ (d : ℤ) - n - A := by
          have : (n : ℤ) + A ≤ d := by exact_mod_cast hle
          omega
        rw [if_pos h0, if_pos hle]
        have htn : ((d : ℤ) - n - A).toNat = d - n - A := by
          omega
        rw [htn]
        push_cast
        ring
      · have h0 : ¬ (0 : ℤ) ≤ (d : ℤ) - n - A := by
          have : ¬ (n : ℤ) + A ≤ d := by
            intro hc; apply hle; exact_mod_cast hc
          omega
        rw [if_neg h0, if_neg hle]
        simp
    rw [hLHS]
    -- RHS side: rewrite each coeff.
    have hRHS :
        (∑ i ∈ Finset.range (d + 1),
            PowerSeries.coeff (R := ℚ) i (qbinomShift k s A)
              * PowerSeries.coeff (R := ℚ) (d - i) (Qgen k))
          = ∑ i ∈ Finset.range (d + 1),
              (if A ≤ i then ((qbinom k s).coeff (i - A) : ℚ) * (partCount k (d - i) : ℚ)
               else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold qbinomShift Qgen
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      by_cases hAi : A ≤ i
      · rw [if_pos hAi, if_pos hAi]
      · rw [if_neg hAi, if_neg hAi]; ring
    rw [hRHS]
    -- Now reindex: bijection n ↦ n + A between nonzero terms.
    -- Both sides are sums over range(d+1). Match via sum over the filtered set.
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_nbij' (fun n => n + A) (fun i => i - A)
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn ⊢
      obtain ⟨hnr, hle⟩ := hn
      exact ⟨by omega, by omega⟩
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
      obtain ⟨hir, hAi⟩ := hi
      exact ⟨by omega, by omega⟩
    · intro n hn
      rw [Finset.mem_filter] at hn
      omega
    · intro i hi
      rw [Finset.mem_filter] at hi
      omega
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnr, hle⟩ := hn
      have h1 : (n + A) - A = n := by omega
      have h2 : d - (n + A) = d - n - A := by omega
      rw [h1, h2]
  -- Assemble the full identity.
  unfold trace numTrace
  ext d
  rw [PowerSeries.coeff_mk]
  rw [Finset.sum_mul, map_sum]
  unfold cCoeff
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  rw [Int.cast_mul, key s d]
  push_cast
  ring

/-- The tail product `∏_{j=2}^k 1/(1-q^j)`. -/
noncomputable def tailGeom (k : ℕ) : PowerSeries ℚ := ∏ j ∈ Finset.Icc 2 k, geom j

theorem tailGeom_nonneg (k n : ℕ) : 0 ≤ PowerSeries.coeff (R := ℚ) n (tailGeom k) := by
  unfold tailGeom
  revert n
  refine Finset.prod_induction _ (fun F => ∀ n, 0 ≤ PowerSeries.coeff (R := ℚ) n F)
    (fun a b ha hb => mul_coeff_nonneg ha hb) ?_ ?_
  · intro n
    simp only [map_one, PowerSeries.coeff_one]
    split <;> norm_num
  · intro j _ n
    exact geom_nonneg j n

theorem Qgen_eq_prod_geom (k : ℕ) : Qgen k = ∏ j ∈ Finset.Icc 1 k, geom j := by
  induction k with
  | zero =>
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by rfl, Finset.prod_empty, Qgen_zero]
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ← ih]
    have hgeom : (1 - PowerSeries.X ^ (k + 1)) * geom (k + 1) = 1 :=
      one_sub_Xpow_mul_geom (k + 1) (by omega)
    have hQ : (1 - (PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) * Qgen (k + 1) = Qgen k :=
      Qgen_succ k
    -- Qgen k * geom (k+1) = ((1-X^(k+1)) * Qgen(k+1)) * geom(k+1)
    --  = Qgen(k+1) * ((1-X^(k+1)) * geom(k+1)) = Qgen(k+1)
    rw [← hQ]
    calc Qgen (k + 1)
        = Qgen (k + 1) * ((1 - PowerSeries.X ^ (k + 1)) * geom (k + 1)) := by
          rw [hgeom, mul_one]
      _ = (1 - (PowerSeries.X : PowerSeries ℚ) ^ (k + 1)) * Qgen (k + 1) * geom (k + 1) := by
          ring

theorem one_sub_X_mul_Qgen_eq_tailGeom (k : ℕ) (hk : 1 ≤ k) :
    (1 - PowerSeries.X) * Qgen k = tailGeom k := by
  rw [Qgen_eq_prod_geom k]
  have hIcc : Finset.Icc 1 k = insert 1 (Finset.Icc 2 k) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1notin : (1 : ℕ) ∉ Finset.Icc 2 k := by
    simp only [Finset.mem_Icc]; omega
  have hpeel : (∏ j ∈ Finset.Icc 1 k, geom j) = geom 1 * tailGeom k := by
    rw [hIcc, Finset.prod_insert h1notin, tailGeom]
  have hg1 : (1 - PowerSeries.X) * geom 1 = 1 := by
    have := one_sub_Xpow_mul_geom 1 (by norm_num)
    rwa [pow_one] at this
  rw [hpeel]
  rw [show (1 - PowerSeries.X) * (geom 1 * tailGeom k)
      = ((1 - PowerSeries.X) * geom 1) * tailGeom k by ring]
  rw [hg1, one_mul]

/-- Shifting a `qbinomShift` by multiplying with `X^c`: `X^c · q^A[k s] = q^{A+c}[k s]`. -/
theorem qbinomShift_shift (k s A c : ℕ) :
    (PowerSeries.X ^ c) * qbinomShift k s A = qbinomShift k s (A + c) := by
  ext n
  rw [PowerSeries.coeff_X_pow_mul']
  unfold qbinomShift
  by_cases hcn : c ≤ n
  · rw [if_pos hcn, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    by_cases hAn : A ≤ n - c
    · rw [if_pos hAn, if_pos (by omega : A + c ≤ n)]
      have hix : n - c - A = n - (A + c) := by omega
      rw [hix]
    · rw [if_neg hAn, if_neg (by omega : ¬ A + c ≤ n)]
  · rw [if_neg hcn, PowerSeries.coeff_mk, if_neg (by omega : ¬ A + c ≤ n)]

/-- Support membership in divisibility form. -/
theorem mem_support_iff_dvd (rho : ℚ) (hrho : 0 < rho) (k s : ℕ) :
    s ∈ support rho k ↔ s ≤ k ∧ rho.den ∣ s := by
  unfold _root_.support
  rw [Finset.mem_filter, Finset.mem_range]
  rw [exponent_den_eq_one_iff rho hrho s]
  omega

/-- Every `s` with `u.den ∣ s` is even when `u.den` is even. -/
theorem U_even {u : ℚ} (hd_even : Even u.den) {s : ℕ} (hs : u.den ∣ s) : Even s := by
  obtain ⟨m, hm⟩ := hd_even
  obtain ⟨t, ht⟩ := hs
  exact ⟨m * t, by rw [ht, hm]; ring⟩

/-- Even elements of `support r k` lie in `support u k` (the `R₊ ⊆ U` inclusion). -/
theorem Rplus_subset_U {u r : ℚ} (hd_dvd : u.den ∣ Nat.lcm r.den 2) {s : ℕ}
    (hrs : r.den ∣ s) (hse : Even s) : u.den ∣ s := by
  have h2 : (2 : ℕ) ∣ s := hse.two_dvd
  have hlcm : Nat.lcm r.den 2 ∣ s := Nat.lcm_dvd hrs h2
  exact dvd_trans hd_dvd hlcm

/-- Monotonicity of the exponent in `ρ` on the support (both integers):
`u ≤ r ⇒ E(s,u) ≤ E(s,r)`.  We assume `E(s,u), E(s,r) ∈ ℤ` (den = 1), which
holds on `R₊ ⊆ support`. -/
theorem exponentNat_mono {u r : ℚ} (hu : 0 < u) (hr : 0 < r) (hur : u ≤ r) (s : ℕ)
    (hsu : (exponent s u).den = 1) (hsr : (exponent s r).den = 1) :
    exponentNat s u ≤ exponentNat s r := by
  -- E(s,u) ≤ E(s,r) as rationals
  have hexp : exponent s u ≤ exponent s r := by
    unfold exponent
    have : (u : ℚ) * s ≤ r * s :=
      mul_le_mul_of_nonneg_right hur (by positivity)
    linarith
  -- when den = 1, (x.num : ℚ) = x
  have hcu : ((exponent s u).num : ℚ) = exponent s u := by
    conv_rhs => rw [← Rat.num_div_den (exponent s u)]
    rw [hsu]; simp
  have hcr : ((exponent s r).num : ℚ) = exponent s r := by
    conv_rhs => rw [← Rat.num_div_den (exponent s r)]
    rw [hsr]; simp
  have hnum : (exponent s u).num ≤ (exponent s r).num := by
    have : ((exponent s u).num : ℚ) ≤ ((exponent s r).num : ℚ) := by
      rw [hcu, hcr]; exact hexp
    exact_mod_cast this
  have hle : exponentInt s u ≤ exponentInt s r := hnum
  unfold exponentNat
  omega

/-- The extraction lemma: `N_{u,k} - N_{r,k} = (1-q)·H` with `H` nonneg. -/
theorem numerator_one_sub_extraction (u r : ℚ) (hu : 0 < u) (hr : 0 < r)
    (hd_even : Even u.den) (hd_dvd : u.den ∣ Nat.lcm r.den 2) (hur : u ≤ r) (k : ℕ) :
    ∃ H : PowerSeries ℚ, (∀ n, 0 ≤ PowerSeries.coeff (R := ℚ) n H) ∧
      numTrace u k - numTrace r k = (1 - PowerSeries.X) * H := by
  classical
  -- Class index sets.  U = support u k (all even); split by r.den ∣ s.
  set HI : PowerSeries ℚ :=
    ∑ s ∈ (support u k).filter (fun s => ¬ r.den ∣ s),
      qbinomShift k s (exponentNat s u) * geom1 with hHI
  set HII : PowerSeries ℚ :=
    ∑ s ∈ (support u k).filter (fun s => r.den ∣ s),
      qbinomShift k s (exponentNat s u) *
        finiteGeom 0 (exponentNat s r - exponentNat s u) with hHII
  set HIII : PowerSeries ℚ :=
    ∑ s ∈ (support r k).filter (fun s => ¬ Even s),
      qbinomShift k s (exponentNat s r) * geom1 with hHIII
  refine ⟨HI + HII + HIII, ?_, ?_⟩
  · -- Nonnegativity: each summand is a product of nonnegative-coeff series.
    intro n
    rw [map_add, map_add]
    have hnnI : 0 ≤ PowerSeries.coeff (R := ℚ) n HI := by
      rw [hHI, map_sum]
      apply Finset.sum_nonneg; intro s _
      exact mul_coeff_nonneg (qbinomShift_nonneg k s _) geom1_nonneg n
    have hnnII : 0 ≤ PowerSeries.coeff (R := ℚ) n HII := by
      rw [hHII, map_sum]
      apply Finset.sum_nonneg; intro s _
      exact mul_coeff_nonneg (qbinomShift_nonneg k s _) (finiteGeom_nonneg _ _) n
    have hnnIII : 0 ≤ PowerSeries.coeff (R := ℚ) n HIII := by
      rw [hHIII, map_sum]
      apply Finset.sum_nonneg; intro s _
      exact mul_coeff_nonneg (qbinomShift_nonneg k s _) geom1_nonneg n
    linarith
  · -- The algebraic identity (1-X)·H = numTrace u - numTrace r.
    -- Abbreviations for the shifted q-binomial series at u and r.
    set Uf := support u k with hUf
    set Rf := support r k with hRf
    -- (1-X)·HI = ∑_{U, ¬r.den∣s} qbShift(u)
    have hEI : (1 - PowerSeries.X) * HI
        = ∑ s ∈ Uf.filter (fun s => ¬ r.den ∣ s),
            qbinomShift k s (exponentNat s u) := by
      rw [hHI, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [show (1 - PowerSeries.X) * (qbinomShift k s (exponentNat s u) * geom1)
          = qbinomShift k s (exponentNat s u) * ((1 - PowerSeries.X) * geom1) by ring,
          one_sub_X_mul_geom1, mul_one]
    -- (1-X)·HIII = ∑_{R-} qbShift(r)
    have hEIII : (1 - PowerSeries.X) * HIII
        = ∑ s ∈ Rf.filter (fun s => ¬ Even s),
            qbinomShift k s (exponentNat s r) := by
      rw [hHIII, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [show (1 - PowerSeries.X) * (qbinomShift k s (exponentNat s r) * geom1)
          = qbinomShift k s (exponentNat s r) * ((1 - PowerSeries.X) * geom1) by ring,
          one_sub_X_mul_geom1, mul_one]
    -- (1-X)·HII = ∑_{U, r.den∣s} (qbShift(u) - qbShift(r))
    have hEII : (1 - PowerSeries.X) * HII
        = ∑ s ∈ Uf.filter (fun s => r.den ∣ s),
            (qbinomShift k s (exponentNat s u) - qbinomShift k s (exponentNat s r)) := by
      rw [hHII, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_filter, hUf, mem_support_iff_dvd u hu k] at hs
      obtain ⟨⟨hsk, hdu⟩, hdr⟩ := hs
      -- s is even (u.den ∣ s, u.den even); s ∈ support r (r.den ∣ s); so s ∈ R₊
      have hse : Even s := U_even hd_even hdu
      -- both exponents are integers on the support
      have hsr' : s ∈ support r k := (mem_support_iff_dvd r hr k s).mpr ⟨hsk, hdr⟩
      have hsu' : s ∈ support u k := (mem_support_iff_dvd u hu k s).mpr ⟨hsk, hdu⟩
      have hAB : exponentNat s u ≤ exponentNat s r := by
        apply exponentNat_mono hu hr hur s
        · have := (Finset.mem_filter.mp hsu').2
          exact (exponent_den_eq_one_iff u hu s).mpr hdu
        · exact (exponent_den_eq_one_iff r hr s).mpr hdr
      set A := exponentNat s u with hA
      set B := exponentNat s r with hB
      -- (1-X)·(qbShift A · finiteGeom 0 (B-A)) = qbShift A · (X^0 - X^(B-A))
      rw [show (1 - PowerSeries.X)
            * (qbinomShift k s A * finiteGeom 0 (B - A))
          = qbinomShift k s A * ((1 - PowerSeries.X) * finiteGeom 0 (B - A)) by ring,
          one_sub_X_mul_finiteGeom (by omega : 0 ≤ B - A)]
      rw [pow_zero, mul_sub, mul_one]
      -- qbShift A · X^(B-A) = X^(B-A) · qbShift A = qbShift (A + (B-A)) = qbShift B
      rw [show qbinomShift k s A * PowerSeries.X ^ (B - A)
          = PowerSeries.X ^ (B - A) * qbinomShift k s A by ring,
          qbinomShift_shift, show A + (B - A) = B by omega]
    -- Combine the three.
    have hsum : (1 - PowerSeries.X) * (HI + HII + HIII)
        = (1 - PowerSeries.X) * HI + (1 - PowerSeries.X) * HII
          + (1 - PowerSeries.X) * HIII := by ring
    rw [hsum, hEI, hEII, hEIII]
    -- Now express numTrace u k and numTrace r k as sums.
    -- numTrace u k = ∑_{s∈U} qbShift(u)  (all signs +1 as U ⊆ evens).
    have hnumU : numTrace u k
        = ∑ s ∈ Uf, qbinomShift k s (exponentNat s u) := by
      rw [hUf]
      unfold numTrace
      apply Finset.sum_congr rfl
      intro s hs
      have hdu : u.den ∣ s := ((mem_support_iff_dvd u hu k s).mp hs).2
      have hse : Even s := U_even hd_even hdu
      rw [hse.neg_one_pow, one_smul]
    -- numTrace r k = ∑_{R+} qbShift(r) - ∑_{R-} qbShift(r).
    have hnumR : numTrace r k
        = ∑ s ∈ Rf.filter (fun s => Even s), qbinomShift k s (exponentNat s r)
          - ∑ s ∈ Rf.filter (fun s => ¬ Even s), qbinomShift k s (exponentNat s r) := by
      rw [hRf]
      unfold numTrace
      rw [← Finset.sum_filter_add_sum_filter_not (support r k) (fun s => Even s)]
      have heven : ∑ s ∈ (support r k).filter (fun s => Even s),
            ((-1 : ℚ) ^ s) • qbinomShift k s (exponentNat s r)
          = ∑ s ∈ (support r k).filter (fun s => Even s),
              qbinomShift k s (exponentNat s r) := by
        apply Finset.sum_congr rfl
        intro s hs
        have : Even s := (Finset.mem_filter.mp hs).2
        rw [this.neg_one_pow, one_smul]
      have hodd : ∑ s ∈ (support r k).filter (fun s => ¬ Even s),
            ((-1 : ℚ) ^ s) • qbinomShift k s (exponentNat s r)
          = - ∑ s ∈ (support r k).filter (fun s => ¬ Even s),
              qbinomShift k s (exponentNat s r) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        have hodd' : Odd s := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hs).2
        rw [hodd'.neg_one_pow, neg_one_smul]
      rw [heven, hodd]
      ring
    rw [hnumU, hnumR]
    -- Now a pure Finset identity.  Split U-sum over (r.den∣s) filter.
    rw [← Finset.sum_filter_add_sum_filter_not Uf (fun s => r.den ∣ s)]
    -- LHS: (∑_{U,r.den∣s} u + ∑_{U,¬r.den∣s} u) - (∑_{R+} r - ∑_{R-} r)
    -- RHS: ∑_{U,¬r.den∣s} u + ∑_{U,r.den∣s}(u - r) + ∑_{R-} r
    -- The R+ = U∩{r.den∣s} identity: on U, s even & r.den∣s ⇔ s ∈ Rf ∧ Even s.
    have hRplusEq :
        (Rf.filter (fun s => Even s)) = (Uf.filter (fun s => r.den ∣ s)) := by
      ext s
      simp only [Finset.mem_filter, hRf, hUf, mem_support_iff_dvd u hu k,
        mem_support_iff_dvd r hr k]
      constructor
      · rintro ⟨⟨hsk, hdr⟩, hse⟩
        exact ⟨⟨hsk, Rplus_subset_U hd_dvd hdr hse⟩, hdr⟩
      · rintro ⟨⟨hsk, hdu⟩, hdr⟩
        exact ⟨⟨hsk, hdr⟩, U_even hd_even hdu⟩
    rw [hRplusEq, Finset.sum_sub_distrib]
    ring

/-! ## Main Statement(s) -/

/-- Statement 1 (Theorem `thm:support-dominance`: Support dominance).
Let `u` and `r` be positive rationals (automatically in lowest terms as
elements of `ℚ`), with `d := den(u)` and `b := den(r)`.  Suppose
(i) `d` is even, (ii) `d ∣ lcm(b,2)`, (iii) `u ≤ r`.  Then for every integer
`k ≥ 1`, `𝒯_{u,k}(q) ⪰_q 𝒯_{r,k}(q)`. -/
theorem support_dominance (u r : ℚ) (hu : 0 < u) (hr : 0 < r)
    (hd_even : Even u.den) (hd_dvd : u.den ∣ Nat.lcm r.den 2) (hur : u ≤ r) :
    ∀ k : ℕ, 1 ≤ k → trace u k ⪰q trace r k := by
  intro k hk n
  obtain ⟨H, hHnn, hH⟩ :=
    numerator_one_sub_extraction u r hu hr hd_even hd_dvd hur k
  rw [map_sub, trace_eq_numTrace_mul_Qgen u hu k, trace_eq_numTrace_mul_Qgen r hr k]
  have hkey : PowerSeries.coeff (R := ℚ) n
      (numTrace u k * Qgen k - numTrace r k * Qgen k)
      = PowerSeries.coeff (R := ℚ) n (H * tailGeom k) := by
    congr 1
    rw [← sub_mul, hH]
    rw [show (1 - PowerSeries.X) * H * Qgen k
        = H * ((1 - PowerSeries.X) * Qgen k) by ring]
    rw [one_sub_X_mul_Qgen_eq_tailGeom k hk]
  rw [← map_sub, hkey]
  exact mul_coeff_nonneg hHnn (tailGeom_nonneg k) n


/-- Statement 2 (Corollary `cor:half-line`: Half-line dominance).
For every rational `r` with `r ≥ 1/2` and every integer `k ≥ 1`,
`𝒯_{1/2,k}(q) ⪰_q 𝒯_{r,k}(q)`. -/
theorem half_line_dominance (r : ℚ) (hr : (1 : ℚ) / 2 ≤ r) :
    ∀ k : ℕ, 1 ≤ k → trace (1 / 2) k ⪰q trace r k := by
  -- Instance of `support_dominance` with `u = 1/2`.  Here `(1/2:ℚ).den = 2`,
  -- which is even and divides `lcm(r.den, 2)`; and `u = 1/2 ≤ r` by hypothesis.
  -- Also need `0 < r` (from `1/2 ≤ r`).
  have hr0 : (0 : ℚ) < r := lt_of_lt_of_le (by norm_num) hr
  have hden : ((1 : ℚ) / 2).den = 2 := by norm_num
  apply support_dominance (1 / 2) r (by norm_num) hr0
  · rw [hden]; exact ⟨1, rfl⟩
  · rw [hden]; exact Nat.dvd_lcm_right _ _
  · exact hr

/-- Denominator of the even core.  For `r > 0`, `evenCore r = 1/L` with
`L = lcm(r.den, 2)`.  Since `L` is a positive even integer, `1/L` is already in
lowest terms with denominator `L`, i.e. `(evenCore r).den = lcm(r.den, 2)`. -/
theorem evenCore_den (r : ℚ) (hr : 0 < r) :
    (evenCore r).den = Nat.lcm r.den 2 := by
  -- `L := lcm(r.den,2) ≥ 2 > 0`, and `1/L = (L:ℚ)⁻¹` with `L` a positive nat is
  -- already reduced; use `Rat.inv_natCast_den_of_pos`.
  have hL : (0 : ℕ) < Nat.lcm r.den 2 := by
    have := r.pos
    exact Nat.lt_of_lt_of_le (by norm_num)
      (Nat.le_of_dvd (by positivity) (Nat.dvd_lcm_right _ _))
  unfold evenCore
  rw [one_div]
  exact Rat.inv_natCast_den_of_pos hL

/-- The even core is `≤ r`.  Since `r ≥ 1/r.den`-style bound: for `r = a/b > 0`
in lowest terms, `evenCore r = 1/lcm(b,2) ≤ 1/b ≤ a/b = r` (as `lcm(b,2) ≥ b`
and `a ≥ 1`). -/
theorem evenCore_le (r : ℚ) (hr : 0 < r) : evenCore r ≤ r := by
  -- `evenCore r = 1/lcm(r.den,2) ≤ 1/r.den` because `r.den ∣ lcm(r.den,2)` so
  -- `lcm(r.den,2) ≥ r.den`.  And `1/r.den ≤ r` since `r = r.num/r.den` with
  -- `r.num ≥ 1` (as `r > 0`), i.e. `r.num ≥ 1 = 1`.  Combine.
  unfold evenCore
  rw [one_div]
  have hbc : (0:ℚ) < (r.den : ℚ) := by exact_mod_cast r.pos
  have hLdvd : r.den ∣ Nat.lcm r.den 2 := Nat.dvd_lcm_left _ _
  have hLge : r.den ≤ Nat.lcm r.den 2 := Nat.le_of_dvd (by positivity) hLdvd
  have hLc : (r.den : ℚ) ≤ (Nat.lcm r.den 2 : ℚ) := by exact_mod_cast hLge
  have h1 : ((Nat.lcm r.den 2 : ℚ))⁻¹ ≤ ((r.den:ℚ))⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hbc]; exact hLc
  have hnumc : (1:ℚ) ≤ (r.num : ℚ) := by
    have := Rat.num_pos.mpr hr; exact_mod_cast (by omega : 1 ≤ r.num)
  have h2 : ((r.den:ℚ))⁻¹ ≤ r := by
    calc ((r.den:ℚ))⁻¹ = 1 / (r.den:ℚ) := by rw [one_div]
      _ ≤ (r.num:ℚ)/(r.den:ℚ) := by
          apply div_le_div_of_nonneg_right hnumc hbc.le
      _ = r := Rat.num_div_den r
  linarith

/-- The denominator of the even core is even. -/
theorem evenCore_den_even (r : ℚ) (hr : 0 < r) : Even (evenCore r).den := by
  -- `(evenCore r).den = lcm(r.den, 2)` (by `evenCore_den`), and `2 ∣ lcm(_,2)`,
  -- so the denominator is even.
  rw [evenCore_den r hr]
  exact ⟨Nat.lcm r.den 2 / 2, by
    have : (2 : ℕ) ∣ Nat.lcm r.den 2 := Nat.dvd_lcm_right _ _
    omega⟩

/-- Statement 3(a) (Theorem `thm:canonical-reduction`, core dominance,
source `eq:core-dominates`).  For every positive rational `r` and every integer
`k ≥ 1`, `𝒯_{r♭,k}(q) ⪰_q 𝒯_{r,k}(q)`, where `r♭` is the even core of `r`. -/
theorem core_dominance (r : ℚ) (hr : 0 < r) :
    ∀ k : ℕ, 1 ≤ k → trace (evenCore r) k ⪰q trace r k := by
  -- Instance of `support_dominance` with `u = evenCore r = 1/lcm(r.den,2)`.
  -- Need: (i) den(evenCore r) even  [evenCore_den_even];
  -- (ii) den(evenCore r) ∣ lcm(r.den,2)  [evenCore_den gives equality, so
  --      divisibility is reflexive];  (iii) evenCore r ≤ r  [evenCore_le].
  -- Also 0 < evenCore r since it is 1/(positive).
  have hL : (0 : ℕ) < Nat.lcm r.den 2 := by
    have := r.pos
    exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (by positivity) (Nat.dvd_lcm_right _ _))
  have hu0 : (0 : ℚ) < evenCore r := by
    unfold evenCore
    have : (0 : ℚ) < (Nat.lcm r.den 2 : ℚ) := by exact_mod_cast hL
    positivity
  apply support_dominance (evenCore r) r hu0 hr
  · exact evenCore_den_even r hr
  · rw [evenCore_den r hr]
  · exact evenCore_le r hr

/-- The even core is a unit-family member: for `r > 0`, `evenCore r = 1/(2m)`
where `2m = lcm(r.den, 2)` (so `m = lcm(r.den,2)/2 ≥ 1`). -/
theorem evenCore_eq_unit (r : ℚ) (_hr : 0 < r) :
    ∃ m : ℕ, 1 ≤ m ∧ evenCore r = 1 / (2 * m) := by
  -- Let `L = lcm(r.den, 2)`.  `2 ∣ L` and `L ≥ 2`, so `m := L/2 ≥ 1` and
  -- `2*m = L`.  Then `evenCore r = 1/L = 1/(2m)`.
  have h2 : (2 : ℕ) ∣ Nat.lcm r.den 2 := Nat.dvd_lcm_right _ _
  have hLpos : 0 < Nat.lcm r.den 2 :=
    Nat.pos_of_ne_zero (fun h => by simp [Nat.lcm_eq_zero_iff] at h)
  have hL2 : 2 ≤ Nat.lcm r.den 2 := Nat.le_of_dvd hLpos h2
  refine ⟨Nat.lcm r.den 2 / 2, ?_, ?_⟩
  · omega
  · unfold evenCore
    have hm : 2 * (Nat.lcm r.den 2 / 2) = Nat.lcm r.den 2 := by omega
    rw [show (2 * ((Nat.lcm r.den 2 / 2 : ℕ) : ℚ)) = ((2 * (Nat.lcm r.den 2 / 2) : ℕ) : ℚ) by push_cast; ring,
        hm]

/-- Statement 3(b), per-`k` equivalence: for every fixed integer `k ≥ 1`,
`HX(k) ⟺ UF(k)`. -/
theorem HXk_iff_UFk (k : ℕ) (hk : 1 ≤ k) : HXk k ↔ UFk k := by
  -- Forward: `HXk k` gives dominance for every `r > 0`, in particular
  -- `r = 1/(2m)` (which is positive for `m ≥ 1`).
  -- Reverse: for arbitrary `r > 0`, write `evenCore r = 1/(2m)` (evenCore_eq_unit);
  -- then `trace (1/2) k ⪰q trace (1/(2m)) k = trace (evenCore r) k` by `UFk`,
  -- and `trace (evenCore r) k ⪰q trace r k` by `core_dominance`; transitivity.
  constructor
  · intro hHX m hm
    have hpos : (0 : ℚ) < 1 / (2 * m) := by
      have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
      positivity
    exact hHX (1 / (2 * m)) hpos
  · intro hUF r hr
    obtain ⟨m, hm, heq⟩ := evenCore_eq_unit r hr
    have h1 : trace (1 / 2) k ⪰q trace (evenCore r) k := by
      rw [heq]; exact hUF m hm
    have h2 : trace (evenCore r) k ⪰q trace r k := core_dominance r hr k hk
    exact coeffLE_trans h1 h2

/-- Statement 3(b) (Theorem `thm:canonical-reduction`, equivalence with the unit
family, source `eq:unit-family`).  The Han–Xiong conjecture `HX` holds iff the
`1/(2m)` unit family holds for all `k` and all `m ≥ 1`. -/
theorem HX_iff_unit_family :
    HX ↔ (∀ k : ℕ, 1 ≤ k → UFk k) := by
  -- `HX := ∀ k ≥ 1, HXk k`; use the per-`k` equivalence `HXk_iff_UFk`.
  constructor
  · intro hHX k hk
    exact (HXk_iff_UFk k hk).mp (hHX k hk)
  · intro hUF k hk
    exact (HXk_iff_UFk k hk).mpr (hUF k hk)

/-- `0 ∈ support (1/2) k` (since `E(0,1/2) = 0 ∈ ℤ`). -/
theorem zero_mem_support_half (k : ℕ) : 0 ∈ support (1 / 2) k := by
  unfold _root_.support
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ?_⟩
  simp [exponent]

/-- Every element of `support (1/2) k` is even, so `(-1)^s = 1` on the support. -/
theorem support_half_even (k : ℕ) {s : ℕ} (hs : s ∈ support (1 / 2) k) : Even s := by
  unfold _root_.support at hs
  rw [Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨_, hden⟩ := hs
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨t, ht⟩ := hodd
  -- E(s,1/2) = s(s+1)/2 + s/2 ; write s(s+1)/2 as a nat cast, den reduces to (s/2).den
  have heven : Even (s * (s + 1)) := Nat.even_mul_succ_self s
  obtain ⟨u, hu⟩ := heven
  have hcast : (s * (s + 1) / 2 : ℚ) = (u : ℚ) := by
    have hh : (s * (s + 1) : ℚ) = ((2 * u : ℕ) : ℚ) := by
      have : s * (s + 1) = 2 * u := by omega
      exact_mod_cast this
    rw [hh]; push_cast; ring
  have hexp : exponent s (1 / 2 : ℚ) = (u : ℚ) + (s : ℚ) / 2 := by
    unfold exponent
    rw [hcast]
    congr 1
    field_simp
  rw [hexp, Rat.natCast_add_den] at hden
  have hdvd : (2 : ℕ) ∣ s := by
    have h2ne : (2 : ℕ) ≠ 0 := by norm_num
    have : ((s : ℚ) / ((2 : ℕ) : ℚ)).den = 1 := by
      rw [show ((2 : ℕ) : ℚ) = (2 : ℚ) by norm_num]; exact hden
    exact (Rat.den_div_natCast_eq_one_iff s 2 h2ne).mp this
  omega

/-- The `1/2` trace dominates `1/(q;q)_k` (the `s=0`-only trace).  This is the
`s=0` dominance fact (source Prop. 5.2 Step 1): for `r=1/2`,
`𝒯_{1/2,k} = 1/(q;q)_k + (nonneg remainder from the even `s>0` terms)`, so
`𝒯_{1/2,k} ⪰q PowerSeries.mk (fun n => p_k(n))` (the reciprocal Pochhammer). -/
theorem half_trace_dominates_recip (k : ℕ) (hk : 1 ≤ k) :
    trace (1 / 2) k ⪰q PowerSeries.mk (fun n => (partCount k n : ℚ)) := by
  -- For `r = 1/2`, `S_{1/2,k} = {0,2,4,…}` and all signs are `+1`, so
  -- `c_{1/2,k}(d) = ∑_{s even} ∑_n β_{k,s}(n) p_k(d-n-E(s,1/2))`, whose `s=0`
  -- term is exactly `p_k(d)` (β_{k,0}=δ_{n,0}, E(0,·)=0) and all other terms are
  -- ≥ 0.  Hence `𝒯_{1/2,k} - (1/(q;q)_k) ⪰q 0` coefficientwise.
  intro d
  -- reduce to integer inequality partCount k d ≤ cCoeff (1/2) k d
  rw [map_sub]
  unfold trace
  simp only [PowerSeries.coeff_mk]
  rw [sub_nonneg]
  have hkey : (partCount k d : ℤ) ≤ cCoeff (1 / 2) k d := by
    -- The summand of cCoeff at each s
    set f : ℕ → ℤ := fun s => (-1) ^ s *
      ∑ n ∈ Finset.range (d + 1),
        betaCoeff k s n * partCountZ k ((d : ℤ) - n - exponentInt s (1 / 2)) with hf
    have hcc : cCoeff (1 / 2) k d = ∑ s ∈ support (1 / 2) k, f s := rfl
    -- 0 ∈ support
    have h0 : (0 : ℕ) ∈ support (1 / 2) k := zero_mem_support_half k
    -- f 0 = partCount k d
    have hbeta0 : ∀ n : ℕ, betaCoeff k 0 n = if n = 0 then 1 else 0 := by
      intro n
      simp only [betaCoeff, qbinom]
      rw [Polynomial.coeff_one]
    have hexp0 : exponentInt 0 (1 / 2 : ℚ) = 0 := by
      simp [exponentInt, exponent]
    have hf0 : f 0 = (partCount k d : ℤ) := by
      rw [hf]
      simp only [pow_zero, one_mul]
      rw [hexp0]
      have hstep : ∀ n ∈ Finset.range (d + 1),
          betaCoeff k 0 n * partCountZ k ((d : ℤ) - n - 0)
            = if n = 0 then (partCount k d : ℤ) else 0 := by
        intro n hn
        rw [hbeta0 n]
        by_cases hn0 : n = 0
        · subst hn0; simp [partCountZ]
        · simp [hn0]
      rw [Finset.sum_congr rfl hstep]
      rw [Finset.sum_ite_eq' (Finset.range (d + 1)) 0 (fun _ => (partCount k d : ℤ))]
      simp
    -- each f s ≥ 0 (sign +1 since s even, inner sum nonneg)
    have hfnn : ∀ s ∈ support (1 / 2) k, 0 ≤ f s := by
      intro s hs
      have hseven : Even s := support_half_even k hs
      have hsign : (-1 : ℤ) ^ s = 1 := hseven.neg_one_pow
      show 0 ≤ (-1 : ℤ) ^ s * _
      rw [hsign, one_mul]
      apply Finset.sum_nonneg
      intro n _
      exact mul_nonneg (betaCoeff_nonneg k s n) (partCountZ_nonneg k _)
    -- split off the 0 term
    rw [hcc, ← Finset.sum_erase_add _ _ h0, hf0]
    have hrest : 0 ≤ ∑ s ∈ (support (1 / 2) k).erase 0, f s := by
      apply Finset.sum_nonneg
      intro s hs
      exact hfnn s (Finset.mem_of_mem_erase hs)
    linarith
  have : ((partCount k d : ℤ) : ℚ) ≤ ((cCoeff (1 / 2) k d : ℤ) : ℚ) := by
    exact_mod_cast hkey
  push_cast at this ⊢
  convert this using 2

/-- For `2m > k` the trace `𝒯_{1/(2m),k}` collapses to `1/(q;q)_k`: the only
`s ∈ {0,…,k}` with `E(s,1/(2m)) ∈ ℤ` is `s=0` (since `E(s,1/(2m)) ∈ ℤ ⟺ 2m ∣ s`
and `0 < s ≤ k < 2m` forbids `2m ∣ s`).  Hence `𝒯_{1/(2m),k} = 1/(q;q)_k`. -/
theorem trace_unit_large (k m : ℕ) (hk : 1 ≤ k) (hm : k < 2 * m) :
    trace (1 / (2 * m)) k = PowerSeries.mk (fun n => (partCount k n : ℚ)) := by
  -- `support (1/(2m)) k = {0}`: for `1 ≤ s ≤ k`, `E(s,1/(2m)) = s(s+1)/2 + s/(2m)`
  -- has `den ≠ 1` because `s/(2m)` is not an integer when `0 < s < 2m`.
  -- Then `c_{1/(2m),k}(d) = (-1)^0 ∑_n β_{k,0}(n) p_k(d-n) = p_k(d)`.
  -- Step 1: support = {0}.
  have hsupp : support (1 / (2 * m)) k = {0} := by
    have hm0 : 0 < m := by omega
    have h2m : (2 * m : ℕ) ≠ 0 := by positivity
    -- den of exponent equals den of s/(2m)
    have hden : ∀ s : ℕ, (exponent s (1 / (2 * (m : ℚ)))).den
        = ((s : ℚ) / (2 * m)).den := by
      intro s
      -- s(s+1)/2 is a natural number cast
      have heven : Even (s * (s + 1)) := Nat.even_mul_succ_self s
      obtain ⟨t, ht⟩ := heven
      have hcast : (s * (s + 1) / 2 : ℚ) = (t : ℚ) := by
        have hh : (s * (s + 1) : ℚ) = ((2 * t : ℕ) : ℚ) := by
          have : s * (s + 1) = 2 * t := by omega
          exact_mod_cast this
        rw [hh]
        push_cast; ring
      have hexp : exponent s (1 / (2 * (m : ℚ)))
          = (t : ℚ) + (s : ℚ) / (2 * m) := by
        unfold exponent
        rw [hcast]
        congr 1
        field_simp
      rw [hexp, Rat.natCast_add_den]
    -- now characterize membership
    ext s
    unfold _root_.support
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hsk, hd⟩
      rw [hden s] at hd
      -- rewrite 2 * (m:ℚ) as ((2*m : ℕ) : ℚ)
      rw [show (2 * (m : ℚ)) = ((2 * m : ℕ) : ℚ) by push_cast; ring] at hd
      -- s/(2m) has denominator 1, so 2m ∣ s
      have hdvd : (2 * m) ∣ s := (Rat.den_div_natCast_eq_one_iff s (2 * m) h2m).mp hd
      -- 0 ≤ s ≤ k < 2m, and 2m ∣ s forces s = 0
      by_contra hs0
      have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      have : 2 * m ≤ s := Nat.le_of_dvd hspos hdvd
      omega
    · rintro rfl
      refine ⟨by omega, ?_⟩
      rw [hden 0]
      simp
  -- Step 2: betaCoeff k 0 n = if n = 0 then 1 else 0
  have hbeta0 : ∀ n : ℕ, betaCoeff k 0 n = if n = 0 then 1 else 0 := by
    intro n
    simp only [betaCoeff, qbinom]
    rw [Polynomial.coeff_one]
  -- Step 3: exponentInt 0 (1/(2m)) = 0
  have hexp0 : exponentInt 0 (1 / (2 * m)) = 0 := by
    simp [exponentInt, exponent]
  -- Step 4: cCoeff (1/(2m)) k d = partCount k d  for all d
  have hc : ∀ d : ℕ, cCoeff (1 / (2 * m)) k d = (partCount k d : ℤ) := by
    intro d
    unfold cCoeff
    rw [hsupp]
    simp only [Finset.sum_singleton, pow_zero, one_mul]
    rw [hexp0]
    have : ∀ n ∈ Finset.range (d + 1),
        betaCoeff k 0 n * partCountZ k ((d : ℤ) - n - 0)
          = if n = 0 then (partCount k d : ℤ) else 0 := by
      intro n hn
      rw [hbeta0 n]
      by_cases hn0 : n = 0
      · subst hn0
        simp [partCountZ]
      · simp [hn0]
    rw [Finset.sum_congr rfl this]
    rw [Finset.sum_ite_eq' (Finset.range (d + 1)) 0 (fun _ => (partCount k d : ℤ))]
    simp
  -- Conclude: the two power series are equal coefficientwise.
  unfold trace
  ext d
  simp only [PowerSeries.coeff_mk]
  rw [hc d]
  push_cast
  ring

/-- Statement 3(c) (Theorem `thm:canonical-reduction`, finite check for fixed
`k`, source `eq:finite-unit-family`).  For every fixed integer `k ≥ 1`, if
`𝒯_{1/2,k}(q) ⪰_q 𝒯_{1/(2m),k}(q)` for every integer `m` with `2 ≤ m ≤ ⌊k/2⌋`,
then `HX(k)` holds.  (When `⌊k/2⌋ < 2`, i.e. `k ≤ 3`, the hypothesis is vacuous
and `HX(k)` holds unconditionally.) -/
theorem finite_unit_family_check (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ m : ℕ, 2 ≤ m → m ≤ k / 2 → trace (1 / 2) k ⪰q trace (1 / (2 * m)) k) :
    HXk k := by
  -- By `HXk_iff_UFk`, suffices `UFk k`, i.e. `∀ m ≥ 1, 𝒯_{1/2,k} ⪰q 𝒯_{1/(2m),k}`.
  -- Case split on m:
  --  • m = 1: `1/(2*1) = 1/2`, dominance is reflexivity (`coeffLE_refl`).
  --  • 2 ≤ m ≤ ⌊k/2⌋: directly from hypothesis `h`.
  --  • m > ⌊k/2⌋ (⇔ 2m > k): `𝒯_{1/(2m),k} = 1/(q;q)_k` (`trace_unit_large`)
  --    and `𝒯_{1/2,k} ⪰q 1/(q;q)_k` (`half_trace_dominates_recip`).
  rw [HXk_iff_UFk k hk]
  intro m hm
  rcases Nat.lt_or_ge (k / 2) m with hlarge | hsmall
  · -- large m: k/2 < m  ⇒  k < 2m
    have h2m : k < 2 * m := by omega
    rw [trace_unit_large k m hk h2m]
    exact half_trace_dominates_recip k hk
  · -- small m: m ≤ k/2
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · -- 2 ≤ m ≤ k/2
      exact h m h1 hsmall
    · -- m = 1  (since 1 ≤ m and m ≤ 1)
      have : m = 1 := by omega
      subst this
      have : (1 : ℚ) / (2 * (1 : ℕ)) = 1 / 2 := by norm_num
      rw [this]
      exact coeffLE_refl _
