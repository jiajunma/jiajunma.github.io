import Mathlib

/-! # Euler's Partition Theorem — constructive bijective proof

Number of partitions of `n` into distinct parts = number into odd parts,
proved via the explicit binary-multiplicity / 2-adic-factorization bijection
in `references/blueprint_verified.md`.
-/

/- USER: HARD CONSTRAINTS for this file (these override the global "prefer Mathlib" rule).

   1. The count equality MUST be proved by the EXPLICIT constructive bijection from
      `references/blueprint_verified.md`: binary digits of the multiplicity of an odd
      part `a` ↔ the distinct parts `2^r · a`. Build Φ (odd→distinct) and Ψ
      (distinct→odd) and prove they are mutually inverse.

   2. FORBIDDEN: do not invoke Mathlib's existing proof of this theorem or any
      generating-function machinery — no `...Partition.GenFun`, `...Partition.Glaisher`,
      `PowerSeries`, and no lemma that already states `#distinct = #odd`. Reprove it.

   3. COMPUTABLE as possible: every definition must be `def` (never `noncomputable`),
      no `Classical.choice` / `open Classical` inside the maps; prefer `Multiset ℕ` /
      `List ℕ` / `Finset` with `DecidableEq`. Φ and Ψ must reduce under `#eval`.
      Add `#eval` / `example` sanity checks (e.g. n = 6 → four partitions each way).

   Suggested order: (a) `two_adic_odd_factorization` lemma; (b) Φ, Ψ; (c) each
   well-defined (sum = n, distinct / odd); (d) `Ψ∘Φ = id`, `Φ∘Ψ = id`; (e) `Equiv`
   and the cardinality corollary `D n = O n`.
-/

open Nat

namespace EulerPartition

/-- Number of partitions of `n` into distinct parts (`#eval`-able). -/
def D (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- Number of partitions of `n` into odd parts (`#eval`-able). -/
def O (n : ℕ) : ℕ := (Nat.Partition.odds n).card

/-! ### (a) 2-adic odd factorization (blueprint `lem:two_adic_odd_factorization`) -/

/-- The representation `2^r * a` with `a` odd is unique (blueprint uniqueness half). -/
theorem two_pow_mul_odd_inj (r a s b : ℕ) (ha : Odd a) (hb : Odd b)
    (h : 2 ^ r * a = 2 ^ s * b) : r = s ∧ a = b := by
  have aux : ∀ (r a s b : ℕ), Odd a → Odd b → r ≤ s →
      2 ^ r * a = 2 ^ s * b → r = s ∧ a = b := by
    intro r a s b ha hb hrs heq
    have ha2 : a = 2 ^ (s - r) * b := by
      have hpow : 2 ^ r * a = 2 ^ r * (2 ^ (s - r) * b) := by
        rw [heq, ← mul_assoc, ← pow_add]
        congr 2
        omega
      exact mul_left_cancel₀ (pow_ne_zero r (by norm_num)) hpow
    rcases Nat.eq_or_lt_of_le hrs with heq' | hlt
    · refine ⟨heq', ?_⟩
      subst heq'
      exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) heq
    · exfalso
      have heven : Even (2 ^ (s - r) * b) :=
        (Nat.even_pow.mpr ⟨by norm_num, by omega⟩).mul_right b
      rw [← ha2] at heven
      exact (Nat.not_even_iff_odd.mpr ha) heven
  rcases le_total r s with hle | hle
  · exact aux r a s b ha hb hle h
  · obtain ⟨e1, e2⟩ := aux s b r a hb ha hle h.symm
    exact ⟨e1.symm, e2.symm⟩

/-- The 2-adic odd part of a nonzero number is odd. -/
theorem odd_ordCompl {x : ℕ} (hx : x ≠ 0) : Odd (ordCompl[2] x) := by
  rw [← Nat.not_even_iff_odd]
  exact fun he => Nat.not_dvd_ordCompl Nat.prime_two hx he.two_dvd

/-- Every positive `x` factors uniquely as `2^r * a` with `a` odd. -/
theorem two_adic_odd_factorization {x : ℕ} (hx : 0 < x) :
    ∃! ra : ℕ × ℕ, Odd ra.2 ∧ x = 2 ^ ra.1 * ra.2 := by
  have hodd : Odd (ordCompl[2] x) := odd_ordCompl hx.ne'
  have heqx : x = 2 ^ x.factorization 2 * ordCompl[2] x :=
    (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
  refine ⟨(x.factorization 2, ordCompl[2] x), ⟨hodd, heqx⟩, ?_⟩
  rintro ⟨s, b⟩ ⟨hb, hxeq⟩
  obtain ⟨e1, e2⟩ := two_pow_mul_odd_inj s b (x.factorization 2) (ordCompl[2] x) hb hodd
    (by rw [← hxeq, ← heqx])
  subst e1; subst e2; rfl

/-! ### (b) Φ : odd → distinct, on the underlying multiset -/

/-- For each distinct value `a` of the odd partition with multiplicity `m = l.count a`,
    emit the parts `2^r * a` for every set bit `r` of `m`. Computable. -/
def phiParts (l : Multiset ℕ) : Multiset ℕ :=
  l.toFinset.val.bind (fun a => ((Nat.bitIndices (l.count a)).map (fun r => 2 ^ r * a) : Multiset ℕ))

/-! ### (c) Ψ : distinct → odd, on the underlying multiset -/

/-- Replace each part `x = 2^r * a` (a odd) by `2^r` copies of `a`. Computable. -/
def psiParts (m : Multiset ℕ) : Multiset ℕ :=
  m.bind (fun x => Multiset.replicate (ordProj[2] x) (ordCompl[2] x))

/-! ### well-definedness obligations -/

theorem phiParts_sum (l : Multiset ℕ) : (phiParts l).sum = l.sum := by
  unfold phiParts
  rw [Multiset.sum_bind]
  have step : (l.toFinset.val.map
      (fun a => (((Nat.bitIndices (l.count a)).map (fun r => 2 ^ r * a) : Multiset ℕ)).sum)).sum
      = (l.toFinset.val.map (fun a => l.count a * a)).sum := by
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    rw [Multiset.sum_coe, List.sum_map_mul_right, Nat.sum_map_two_pow_bitIndices]
  rw [step]
  conv_rhs => rw [← Multiset.map_id l]
  rw [Finset.sum_multiset_map_count l id]
  simp only [id_eq, smul_eq_mul]
  rfl

theorem phiParts_pos {l : Multiset ℕ} (hl : ∀ i ∈ l, 0 < i) : ∀ i ∈ phiParts l, 0 < i := by
  intro i hi
  unfold phiParts at hi
  rw [Multiset.mem_bind] at hi
  obtain ⟨a, ha, hi⟩ := hi
  rw [Multiset.mem_coe, List.mem_map] at hi
  obtain ⟨r, _, rfl⟩ := hi
  have ha' : a ∈ l := Multiset.mem_toFinset.mp (Finset.mem_val.mp ha)
  exact Nat.mul_pos (by positivity) (hl a ha')

theorem phiParts_nodup {l : Multiset ℕ} (hodd : ∀ i ∈ l, ¬ Even i) : (phiParts l).Nodup := by
  have hoddF : ∀ a ∈ l.toFinset, Odd a := fun a ha =>
    Nat.not_even_iff_odd.mp (hodd a (Multiset.mem_toFinset.mp ha))
  unfold phiParts
  rw [Multiset.nodup_bind]
  refine ⟨?_, ?_⟩
  · intro a ha
    have haodd : Odd a := hoddF a (Finset.mem_val.mp ha)
    have ha_pos : 0 < a := haodd.pos
    rw [Multiset.coe_nodup]
    apply Nat.bitIndices_nodup.map
    intro r s hrs
    have h2 : (2 : ℕ) ^ r = 2 ^ s := Nat.eq_of_mul_eq_mul_right ha_pos hrs
    exact Nat.pow_right_injective (le_refl 2) h2
  · apply Multiset.Nodup.pairwise (s := l.toFinset.val)
    · intro a ha b hb hab
      have haodd : Odd a := hoddF a (Finset.mem_val.mp ha)
      have hbodd : Odd b := hoddF b (Finset.mem_val.mp hb)
      simp only [Function.onFun, Multiset.disjoint_left]
      intro y hya hyb
      rw [Multiset.mem_coe, List.mem_map] at hya hyb
      obtain ⟨r, _, hr⟩ := hya
      obtain ⟨s, _, hs⟩ := hyb
      have := two_pow_mul_odd_inj r a s b haodd hbodd (by rw [hr, hs])
      exact hab this.2
    · exact l.toFinset.nodup

theorem psiParts_sum (m : Multiset ℕ) (hm : ∀ i ∈ m, 0 < i) : (psiParts m).sum = m.sum := by
  unfold psiParts
  rw [Multiset.sum_bind]
  conv_rhs => rw [← Multiset.map_id m]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  rw [Multiset.sum_replicate, smul_eq_mul, Nat.ordProj_mul_ordCompl_eq_self, id_eq]

theorem psiParts_pos {m : Multiset ℕ} (hm : ∀ i ∈ m, 0 < i) : ∀ i ∈ psiParts m, 0 < i := by
  intro i hi
  unfold psiParts at hi
  rw [Multiset.mem_bind] at hi
  obtain ⟨x, hx, hi⟩ := hi
  rw [Multiset.mem_replicate] at hi
  obtain ⟨_, rfl⟩ := hi
  exact Nat.ordCompl_pos 2 (hm x hx).ne'

theorem psiParts_odd {m : Multiset ℕ} (hm : ∀ i ∈ m, 0 < i) : ∀ i ∈ psiParts m, ¬ Even i := by
  intro i hi
  unfold psiParts at hi
  rw [Multiset.mem_bind] at hi
  obtain ⟨x, hx, hi⟩ := hi
  rw [Multiset.mem_replicate] at hi
  obtain ⟨_, rfl⟩ := hi
  intro h
  exact Nat.not_dvd_ordCompl Nat.prime_two (hm x hx).ne' h.two_dvd

/-! ### helper identities for the round trips -/

/-- For `a` odd, the 2-adic data of `2^r * a` is exactly `(r, a)`. -/
theorem ord_two_pow_mul_odd {r a : ℕ} (ha : Odd a) :
    (2 ^ r * a).factorization 2 = r ∧ ordCompl[2] (2 ^ r * a) = a := by
  have hapos : 0 < a := ha.pos
  have hx : 0 < 2 ^ r * a := by positivity
  have hodd : Odd (ordCompl[2] (2 ^ r * a)) := odd_ordCompl hx.ne'
  have heqx : 2 ^ r * a = 2 ^ (2 ^ r * a).factorization 2 * ordCompl[2] (2 ^ r * a) :=
    (Nat.ordProj_mul_ordCompl_eq_self (2 ^ r * a) 2).symm
  obtain ⟨e1, e2⟩ := two_pow_mul_odd_inj r a ((2 ^ r * a).factorization 2)
    (ordCompl[2] (2 ^ r * a)) ha hodd heqx
  exact ⟨e1.symm, e2.symm⟩

/-- `bind` of `replicate (2^r) a` over the set bits of `m` collapses to `replicate m a`. -/
theorem bind_replicate_two_pow (a m : ℕ) :
    (↑(Nat.bitIndices m) : Multiset ℕ).bind (fun r => Multiset.replicate (2 ^ r) a)
      = Multiset.replicate m a := by
  rw [Multiset.eq_replicate]
  refine ⟨?_, ?_⟩
  · rw [Multiset.card_bind]
    simp only [Function.comp, Multiset.card_replicate]
    rw [Multiset.map_coe, Multiset.sum_coe]
    exact Nat.sum_map_two_pow_bitIndices m
  · intro b hb
    rw [Multiset.mem_bind] at hb
    obtain ⟨r, _, hb⟩ := hb
    rw [Multiset.mem_replicate] at hb
    exact hb.2

/-- Reconstruct a multiset from its `toFinset` and multiplicities. -/
theorem toFinset_bind_replicate_count (l : Multiset ℕ) :
    l.toFinset.val.bind (fun a => Multiset.replicate (l.count a) a) = l := by
  ext c
  rw [Multiset.count_bind]
  simp only [Multiset.count_replicate]
  rw [show (Multiset.map (fun x => if x = c then l.count x else 0) l.toFinset.val).sum
        = ∑ x ∈ l.toFinset, (if x = c then l.count x else 0) from rfl]
  rw [Finset.sum_ite_eq']
  split_ifs with hc
  · rfl
  · exact (Multiset.count_eq_zero.mpr (fun h => hc (Multiset.mem_toFinset.mpr h))).symm

/-- `Ψ ∘ Φ = id` on the underlying multiset of an odd partition. -/
theorem psiParts_phiParts {l : Multiset ℕ} (hodd : ∀ i ∈ l, ¬ Even i) :
    psiParts (phiParts l) = l := by
  have hoddF : ∀ a ∈ l.toFinset, Odd a := fun a ha =>
    Nat.not_even_iff_odd.mp (hodd a (Multiset.mem_toFinset.mp ha))
  unfold psiParts phiParts
  rw [Multiset.bind_assoc]
  refine (Multiset.bind_congr ?_).trans (toFinset_bind_replicate_count l)
  intro a ha
  have haodd : Odd a := hoddF a (Finset.mem_val.mp ha)
  rw [← Multiset.map_coe, Multiset.bind_map, ← bind_replicate_two_pow a (l.count a)]
  apply Multiset.bind_congr
  intro r _
  obtain ⟨hf, hc⟩ := ord_two_pow_mul_odd (r := r) haodd
  show Multiset.replicate (ordProj[2] (2 ^ r * a)) (ordCompl[2] (2 ^ r * a))
      = Multiset.replicate (2 ^ r) a
  rw [hc]
  congr 1
  rw [hf]

/-- For `a` odd and `m` distinct, the set bits of `count a (Ψ m)` are exactly the `r`
    with `2^r·a ∈ m`. This is the heart of `Φ ∘ Ψ = id`. -/
theorem mem_bitIndices_count_psiParts {m : Multiset ℕ} (hnodup : m.Nodup)
    {a : ℕ} (ha : Odd a) (r : ℕ) :
    r ∈ Nat.bitIndices ((psiParts m).count a) ↔ 2 ^ r * a ∈ m := by
  set S : Finset ℕ :=
    (m.toFinset.filter (fun x => ordCompl[2] x = a)).image (fun x => x.factorization 2) with hS
  have hinj : Set.InjOn (fun x : ℕ => x.factorization 2)
      (↑(m.toFinset.filter (fun x => ordCompl[2] x = a)) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Multiset.mem_toFinset] at hx hy
    have hfe : x.factorization 2 = y.factorization 2 := hxy
    have hxe : x = 2 ^ (x.factorization 2) * ordCompl[2] x :=
      (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
    rw [hxe, hx.2, hfe, ← hy.2]
    exact Nat.ordProj_mul_ordCompl_eq_self y 2
  have hcount : (psiParts m).count a = ∑ i ∈ S, 2 ^ i := by
    unfold psiParts
    rw [Multiset.count_bind]
    simp only [Multiset.count_replicate]
    have hsum : (Multiset.map (fun x => if ordCompl[2] x = a then ordProj[2] x else 0) m).sum
        = ∑ x ∈ m.toFinset, (if ordCompl[2] x = a then ordProj[2] x else 0) := by
      show _ = (Multiset.map _ m.toFinset.val).sum
      rw [Multiset.toFinset_val, hnodup.dedup]
    rw [hsum, ← Finset.sum_filter, hS, Finset.sum_image hinj]
  rw [hcount, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow, hS]
  simp only [Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · rintro ⟨x, ⟨hxm, hax⟩, hxr⟩
    have hx2 : x = 2 ^ r * a := by
      rw [← hxr, ← hax]; exact (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
    rwa [← hx2]
  · intro hmem
    obtain ⟨hf, hc⟩ := ord_two_pow_mul_odd (r := r) ha
    exact ⟨2 ^ r * a, ⟨hmem, hc⟩, hf⟩

/-- `Φ ∘ Ψ = id` on the underlying multiset of a distinct partition. -/
theorem phiParts_psiParts {m : Multiset ℕ} (hpos : ∀ i ∈ m, 0 < i) (hnodup : m.Nodup) :
    phiParts (psiParts m) = m := by
  have hodd : ∀ i ∈ psiParts m, ¬ Even i := psiParts_odd hpos
  refine (Multiset.Nodup.ext (phiParts_nodup hodd) hnodup).mpr (fun x => ?_)
  constructor
  · intro hx
    unfold phiParts at hx
    rw [Multiset.mem_bind] at hx
    obtain ⟨a, ha, hx⟩ := hx
    rw [Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have haodd : Odd a :=
      Nat.not_even_iff_odd.mp (hodd a (Multiset.mem_toFinset.mp (Finset.mem_val.mp ha)))
    exact (mem_bitIndices_count_psiParts hnodup haodd r).mp hr
  · intro hx
    have hxpos : 0 < x := hpos x hx
    have hxodd : Odd (ordCompl[2] x) := odd_ordCompl hxpos.ne'
    have hxeq : x = 2 ^ (x.factorization 2) * ordCompl[2] x :=
      (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
    unfold phiParts
    rw [Multiset.mem_bind]
    refine ⟨ordCompl[2] x, ?_, ?_⟩
    · rw [Finset.mem_val, Multiset.mem_toFinset]
      show ordCompl[2] x ∈ Multiset.bind m
        (fun y => Multiset.replicate (ordProj[2] y) (ordCompl[2] y))
      rw [Multiset.mem_bind]
      exact ⟨x, hx, Multiset.mem_replicate.mpr
        ⟨(by positivity : (0 : ℕ) < ordProj[2] x).ne', rfl⟩⟩
    · rw [Multiset.mem_coe, List.mem_map]
      refine ⟨x.factorization 2, ?_, hxeq.symm⟩
      have hmem : 2 ^ (x.factorization 2) * ordCompl[2] x ∈ m := hxeq ▸ hx
      exact (mem_bitIndices_count_psiParts hnodup hxodd (x.factorization 2)).mpr hmem

/-! ### bundled maps on `Nat.Partition` (proof fields may be `sorry` for now) -/

def Phi {n : ℕ} (p : n.Partition) : n.Partition :=
  ⟨phiParts p.parts,
   fun {i} hi => phiParts_pos (fun j hj => p.parts_pos hj) i hi,
   by rw [phiParts_sum]; exact p.parts_sum⟩
def Psi {n : ℕ} (p : n.Partition) : n.Partition :=
  ⟨psiParts p.parts,
   fun {i} hi => psiParts_pos (fun j hj => p.parts_pos hj) i hi,
   by rw [psiParts_sum p.parts (fun j hj => p.parts_pos hj)]; exact p.parts_sum⟩

/-! ### Φ, Ψ land in the right Finsets -/

theorem Phi_mem_distincts {n : ℕ} {p : n.Partition} (hp : p ∈ Nat.Partition.odds n) :
    Phi p ∈ Nat.Partition.distincts n := by
  have hodd : ∀ i ∈ p.parts, ¬ Even i := by
    unfold Nat.Partition.odds Nat.Partition.restricted at hp
    simpa using hp
  unfold Nat.Partition.distincts
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact phiParts_nodup hodd
theorem Psi_mem_odds {n : ℕ} {p : n.Partition} (hp : p ∈ Nat.Partition.distincts n) :
    Psi p ∈ Nat.Partition.odds n := by
  unfold Nat.Partition.odds Nat.Partition.restricted
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact psiParts_odd (fun j hj => p.parts_pos hj)

/-! ### (f) mutually inverse -/

theorem Psi_Phi {n : ℕ} {p : n.Partition} (hp : p ∈ Nat.Partition.odds n) : Psi (Phi p) = p := by
  have hodd : ∀ i ∈ p.parts, ¬ Even i := by
    unfold Nat.Partition.odds Nat.Partition.restricted at hp
    simpa using hp
  apply Nat.Partition.ext
  show psiParts (phiParts p.parts) = p.parts
  exact psiParts_phiParts hodd
theorem Phi_Psi {n : ℕ} {p : n.Partition} (hp : p ∈ Nat.Partition.distincts n) : Phi (Psi p) = p := by
  have hnodup : p.parts.Nodup := by
    unfold Nat.Partition.distincts at hp
    simpa using hp
  apply Nat.Partition.ext
  show phiParts (psiParts p.parts) = p.parts
  exact phiParts_psiParts (fun j hj => p.parts_pos hj) hnodup

/-! ### (g) final bijection and count equality -/

theorem euler_partition (n : ℕ) : D n = O n := by
  unfold D O
  exact Finset.card_nbij' Psi Phi
    (fun p hp => Psi_mem_odds hp)
    (fun p hp => Phi_mem_distincts hp)
    (fun p hp => Phi_Psi hp)
    (fun p hp => Psi_Phi hp)

/-! ### sanity checks -/

#eval D 6  -- expect 4
#eval O 6  -- expect 4
#eval phiParts {1,1,1,1,1,3}      -- some distinct multiset summing to 6 (informal check)
#eval psiParts {4,2}              -- → odd parts summing to 6

end EulerPartition
