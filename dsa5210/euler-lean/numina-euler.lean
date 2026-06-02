import Mathlib

/-!
# Euler's Partition Theorem — formalize FOLLOWING the blueprint

Source of truth (statement AND proof): `references/blueprint_verified.md`.

Render the blueprint into Lean and prove it sorry-free, following the blueprint's
own proof closely. Do NOT invent an alternative proof.

The blueprint has two named items, both to be proved:

* `lem:two_adic_odd_factorization` — every positive integer is uniquely `2^r * a`
  with `a` odd.
* `thm:euler_partition_bijection` — `D(n) = O(n)`, proved by the EXPLICIT bijection
  `Φ` (odd → distinct) / `Ψ` (distinct → odd) of the blueprint.

Only the two statements below are fixed targets; add exactly the auxiliary `def`s and
lemmas the blueprint's proof uses (the maps `Φ`, `Ψ`, their well-definedness, and
that they are mutually inverse), then conclude.

Constraints: follow `references/blueprint_verified.md` closely; keep everything as
computable as possible (auxiliary maps are plain `def`s, no `noncomputable`, no
`Classical.choice`/`open Classical` inside them, reducing under `#eval`); do NOT use
Mathlib's `Nat.Partition.card_odds_eq_card_distincts` (Glaisher) or any
`PowerSeries`/generating-function route; no new `axiom`s.
-/

open Nat

namespace EulerPartition

/-- Number of partitions of `n` into distinct parts. Blueprint `D(n)`. Computable. -/
def D (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- Number of partitions of `n` into odd parts. Blueprint `O(n)`. Computable. -/
def O (n : ℕ) : ℕ := (Nat.Partition.odds n).card

/-! ### 2-adic odd factorization helpers -/

/-- An odd natural number is not divisible by `2`. -/
lemma not_two_dvd_of_odd {a : ℕ} (ha : Odd a) : ¬ (2 ∣ a) :=
  Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp ha)

/-- For odd `a`, `ordCompl[2] (2 ^ r * a) = a`. -/
lemma ordCompl_two_pow_mul {a : ℕ} (ha : Odd a) (r : ℕ) :
    ordCompl[2] (2 ^ r * a) = a :=
  Nat.ordCompl_pow_mul_of_not_dvd r Nat.prime_two (not_two_dvd_of_odd ha)

/-- For odd `a`, `ordProj[2] (2 ^ r * a) = 2 ^ r`. -/
lemma ordProj_two_pow_mul {a : ℕ} (ha : Odd a) (r : ℕ) :
    ordProj[2] (2 ^ r * a) = 2 ^ r := by
  have hpos : 0 < a := ha.pos
  have key := Nat.ordProj_mul_ordCompl_eq_self (2 ^ r * a) 2
  rw [ordCompl_two_pow_mul ha r] at key
  exact Nat.eq_of_mul_eq_mul_right hpos key

/-- Blueprint `lem:two_adic_odd_factorization`:
every positive integer `x` is uniquely of the form `2 ^ r * a` with `a` odd. -/
theorem two_adic_odd_factorization {x : ℕ} (hx : 0 < x) :
    ∃! ra : ℕ × ℕ, Odd ra.2 ∧ x = 2 ^ ra.1 * ra.2 := by
  have hx0 : x ≠ 0 := hx.ne'
  refine ⟨(x.factorization 2, ordCompl[2] x), ⟨?_, ?_⟩, ?_⟩
  · -- `ordCompl[2] x` is odd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hx0))
  · -- `x = 2 ^ (factorization) * ordCompl`
    exact (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
  · -- uniqueness
    rintro ⟨s, b⟩ ⟨hb, hxb⟩
    have hcompl : ordCompl[2] x = b := by rw [hxb]; exact ordCompl_two_pow_mul hb s
    have hproj : ordProj[2] x = 2 ^ s := by rw [hxb]; exact ordProj_two_pow_mul hb s
    have hs : x.factorization 2 = s :=
      Nat.pow_right_injective (le_refl 2) hproj
    simp only [Prod.mk.injEq]
    exact ⟨hs.symm, hcompl.symm⟩

/-! ### The map `Ψ` : distinct parts → odd parts

`Ψ` replaces each part `x = 2^r·a` (with `a` odd) by `2^r` copies of `a`. -/

/-- `Ψ` on multisets. Computable: no `Classical`, plain `Multiset.bind`. -/
def psi (μ : Multiset ℕ) : Multiset ℕ :=
  μ.bind fun x => Multiset.replicate (ordProj[2] x) (ordCompl[2] x)

/-- Count formula for `Ψ`. -/
lemma count_psi (μ : Multiset ℕ) (c : ℕ) :
    (psi μ).count c = (μ.map fun x => if ordCompl[2] x = c then ordProj[2] x else 0).sum := by
  rw [psi, Multiset.count_bind]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  rw [Multiset.count_replicate]

/-- `Ψ` preserves the sum of parts. -/
lemma psi_sum (μ : Multiset ℕ) : (psi μ).sum = μ.sum := by
  rw [psi, Multiset.sum_bind]
  conv_rhs => rw [← Multiset.map_id μ]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  rw [Multiset.sum_replicate, smul_eq_mul, Nat.ordProj_mul_ordCompl_eq_self, id]

/-- Every part of `Ψ μ` is positive (given the parts of `μ` are). -/
lemma psi_pos {μ : Multiset ℕ} (h : ∀ x ∈ μ, 0 < x) : ∀ y ∈ psi μ, 0 < y := by
  intro y hy
  rw [psi, Multiset.mem_bind] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Multiset.mem_replicate] at hy
  obtain ⟨_, rfl⟩ := hy
  exact Nat.ordCompl_pos 2 (h x hx).ne'

/-- Every part of `Ψ μ` is odd (given the parts of `μ` are positive). -/
lemma psi_odd {μ : Multiset ℕ} (h : ∀ x ∈ μ, 0 < x) : ∀ y ∈ psi μ, ¬ Even y := by
  intro y hy
  rw [psi, Multiset.mem_bind] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Multiset.mem_replicate] at hy
  obtain ⟨_, rfl⟩ := hy
  intro hev
  exact Nat.not_dvd_ordCompl Nat.prime_two (h x hx).ne' hev.two_dvd

/-! ### The map `Φ` : odd parts → distinct parts

For each distinct part `a` of multiplicity `m`, `Φ` emits the parts `2^r·a`
for the positions `r` of the `1`-bits in the binary expansion of `m`. -/

/-- `Φ` on multisets. Computable: `Finset.sum` over `Nat.bitIndices`. -/
def phi (l : Multiset ℕ) : Multiset ℕ :=
  ∑ a ∈ l.toFinset, ((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a : Multiset ℕ)

/-- Count of a positive value `y` in one `Φ`-block for an odd base `a`. -/
lemma count_oddBlock {a : ℕ} (ha : Odd a) (m : ℕ) {y : ℕ} (hy : 0 < y) :
    Multiset.count y ((Nat.bitIndices m).map fun r => 2 ^ r * a : Multiset ℕ)
      = if a = ordCompl[2] y ∧ y.factorization 2 ∈ Nat.bitIndices m then 1 else 0 := by
  have hinj : Function.Injective (fun r => 2 ^ r * a) := by
    intro r s hrs
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right ha.pos hrs)
  have hmem : y ∈ ((Nat.bitIndices m).map fun r => 2 ^ r * a : Multiset ℕ)
      ↔ a = ordCompl[2] y ∧ y.factorization 2 ∈ Nat.bitIndices m := by
    rw [Multiset.mem_coe, List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨(ordCompl_two_pow_mul ha r).symm, ?_⟩
      have hfac : (2 ^ r * a).factorization 2 = r :=
        Nat.pow_right_injective (le_refl 2) (ordProj_two_pow_mul ha r)
      rwa [hfac]
    · rintro ⟨hac, hfac⟩
      refine ⟨y.factorization 2, hfac, ?_⟩
      rw [hac]
      exact Nat.ordProj_mul_ordCompl_eq_self y 2
  have hnodup : ((Nat.bitIndices m).map fun r => 2 ^ r * a : Multiset ℕ).Nodup := by
    rw [Multiset.coe_nodup]
    exact Nat.bitIndices_nodup.map hinj
  by_cases h : a = ordCompl[2] y ∧ y.factorization 2 ∈ Nat.bitIndices m
  · rw [if_pos h]
    exact Multiset.count_eq_one_of_mem hnodup (hmem.mpr h)
  · rw [if_neg h, Multiset.count_eq_zero]
    exact fun hc => h (hmem.mp hc)

/-- Count formula for `Φ` at a positive value, when all parts of `l` are odd. -/
lemma count_phi {l : Multiset ℕ} (hl : ∀ a ∈ l, Odd a) {y : ℕ} (hy : 0 < y) :
    (phi l).count y
      = if y.factorization 2 ∈ Nat.bitIndices (l.count (ordCompl[2] y)) then 1 else 0 := by
  rw [phi, Multiset.count_sum']
  have step : ∀ a ∈ l.toFinset,
      Multiset.count y ((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a : Multiset ℕ)
        = if a = ordCompl[2] y then
            (if y.factorization 2 ∈ Nat.bitIndices (l.count a) then 1 else 0) else 0 := by
    intro a ha
    rw [count_oddBlock (hl a (Multiset.mem_toFinset.mp ha)) (l.count a) hy]
    by_cases hh : a = ordCompl[2] y <;> simp [hh]
  rw [Finset.sum_congr rfl step,
      Finset.sum_ite_eq' l.toFinset (ordCompl[2] y)
        (fun a => if y.factorization 2 ∈ Nat.bitIndices (l.count a) then 1 else 0)]
  by_cases hmem : ordCompl[2] y ∈ l.toFinset
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    have hc : l.count (ordCompl[2] y) = 0 :=
      Multiset.count_eq_zero.mpr (fun hc => hmem (Multiset.mem_toFinset.mpr hc))
    rw [hc]
    simp

/-- `Φ` preserves the sum of parts. -/
lemma phi_sum (l : Multiset ℕ) : (phi l).sum = l.sum := by
  rw [phi]
  have hdist : (∑ a ∈ l.toFinset,
      ((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a : Multiset ℕ)).sum
      = ∑ a ∈ l.toFinset,
          ((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a : Multiset ℕ).sum := by
    simp only [← Multiset.coe_sumAddMonoidHom, map_sum]
  rw [hdist]
  conv_rhs => rw [Finset.sum_multiset_count l]
  apply Finset.sum_congr rfl
  intro a _
  rw [Multiset.sum_coe, List.sum_map_mul_right, Nat.sum_map_two_pow_bitIndices, smul_eq_mul]

/-- `Φ l` has distinct parts when all parts of `l` are odd. -/
lemma phi_nodup {l : Multiset ℕ} (hl : ∀ a ∈ l, Odd a) : (phi l).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have h0 : (0 : ℕ) ∉ phi l := by
      intro h0
      rw [phi, Multiset.mem_sum] at h0
      obtain ⟨a, ha, h0⟩ := h0
      have hapos : 0 < a := (hl a (Multiset.mem_toFinset.mp ha)).pos
      rw [Multiset.mem_coe, List.mem_map] at h0
      obtain ⟨r, _, hr⟩ := h0
      have : 0 < 2 ^ r * a := Nat.mul_pos (pow_pos (by norm_num) r) hapos
      omega
    rw [Multiset.count_eq_zero.mpr h0]
    omega
  · rw [count_phi hl hy]
    split <;> simp

/-- Every part of `Φ l` is positive (given all parts of `l` are positive). -/
lemma phi_pos {l : Multiset ℕ} (hl : ∀ a ∈ l, 0 < a) : ∀ y ∈ phi l, 0 < y := by
  intro y hy
  rw [phi, Multiset.mem_sum] at hy
  obtain ⟨a, ha, hy⟩ := hy
  have hapos : 0 < a := hl a (Multiset.mem_toFinset.mp ha)
  rw [Multiset.mem_coe, List.mem_map] at hy
  obtain ⟨r, _, hr⟩ := hy
  rw [← hr]
  exact Nat.mul_pos (pow_pos (by norm_num) r) hapos

/-! ### `Ψ ∘ Φ = id` (on odd partitions) -/

/-- `Multiset.map` then `Multiset.sum` distribute over a `Finset.sum` of multisets. -/
lemma map_sum_sum_distrib {ι : Type*} (s : Finset ι) (B : ι → Multiset ℕ) (g : ℕ → ℕ) :
    ((∑ a ∈ s, B a).map g).sum = ∑ a ∈ s, ((B a).map g).sum := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Multiset.map_add, Multiset.sum_add, ih, Finset.sum_cons]

/-- Summing `Ψ`'s weight over a single `Φ`-block recovers the multiplicity (or `0`). -/
lemma sum_map_g_oddBlock {a c : ℕ} (ha : Odd a) (m : ℕ) :
    (((Nat.bitIndices m).map fun r => 2 ^ r * a : Multiset ℕ).map
        fun x => if ordCompl[2] x = c then ordProj[2] x else 0).sum
      = if a = c then m else 0 := by
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  by_cases h : a = c
  · subst h
    have hmap : ((Nat.bitIndices m).map
        ((fun x => if ordCompl[2] x = a then ordProj[2] x else 0) ∘ fun r => 2 ^ r * a))
        = (Nat.bitIndices m).map fun r => 2 ^ r := by
      apply List.map_congr_left
      intro r _
      rw [Function.comp_apply, ordCompl_two_pow_mul ha r, ordProj_two_pow_mul ha r]
      simp
    rw [hmap, Nat.sum_map_two_pow_bitIndices, if_pos rfl]
  · have hmap : ((Nat.bitIndices m).map
        ((fun x => if ordCompl[2] x = c then ordProj[2] x else 0) ∘ fun r => 2 ^ r * a))
        = (Nat.bitIndices m).map fun _ => 0 := by
      apply List.map_congr_left
      intro r _
      rw [Function.comp_apply, ordCompl_two_pow_mul ha r, if_neg h]
    rw [hmap, if_neg h]
    simp

/-- Right inverse: `Ψ (Φ l) = l` for `l` with all parts odd. -/
lemma psi_phi {l : Multiset ℕ} (hl : ∀ a ∈ l, Odd a) : psi (phi l) = l := by
  ext c
  rw [count_psi, phi, map_sum_sum_distrib]
  have step : ∀ a ∈ l.toFinset,
      (((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a : Multiset ℕ).map
          fun x => if ordCompl[2] x = c then ordProj[2] x else 0).sum
        = if a = c then l.count a else 0 := by
    intro a ha
    exact sum_map_g_oddBlock (hl a (Multiset.mem_toFinset.mp ha)) (l.count a)
  rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' l.toFinset c (fun a => l.count a)]
  by_cases hmem : c ∈ l.toFinset
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    exact (Multiset.count_eq_zero.mpr (fun hc => hmem (Multiset.mem_toFinset.mpr hc))).symm

/-! ### `Φ ∘ Ψ = id` (on distinct partitions) -/

/-- Left inverse: `Φ (Ψ μ) = μ` for `μ` with distinct, positive parts. -/
lemma phi_psi {μ : Multiset ℕ} (hμ : μ.Nodup) (hpos : ∀ x ∈ μ, 0 < x) : phi (psi μ) = μ := by
  have hodd : ∀ a ∈ psi μ, Odd a := fun a ha => Nat.not_even_iff_odd.mp (psi_odd hpos a ha)
  ext y
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have h1 : (0 : ℕ) ∉ phi (psi μ) := fun h => absurd (phi_pos (psi_pos hpos) 0 h) (lt_irrefl 0)
    have h2 : (0 : ℕ) ∉ μ := fun h => absurd (hpos 0 h) (lt_irrefl 0)
    rw [Multiset.count_eq_zero.mpr h1, Multiset.count_eq_zero.mpr h2]
  · rw [count_phi hodd hy, Multiset.count_eq_of_nodup hμ]
    set a₀ := ordCompl[2] y with ha₀
    set s₀ := y.factorization 2 with hs₀def
    have hyeq : 2 ^ s₀ * a₀ = y := Nat.ordProj_mul_ordCompl_eq_self y 2
    -- injectivity of the exponent map on the relevant fibre
    have hinj : ∀ x ∈ μ.toFinset.filter (fun m => ordCompl[2] m = a₀),
        ∀ z ∈ μ.toFinset.filter (fun m => ordCompl[2] m = a₀),
        x.factorization 2 = z.factorization 2 → x = z := by
      intro x hx z hz hxz
      rw [Finset.mem_filter] at hx hz
      have ex : x = 2 ^ x.factorization 2 * a₀ := by
        rw [← hx.2]; exact (Nat.ordProj_mul_ordCompl_eq_self x 2).symm
      have ez : z = 2 ^ z.factorization 2 * a₀ := by
        rw [← hz.2]; exact (Nat.ordProj_mul_ordCompl_eq_self z 2).symm
      calc x = 2 ^ x.factorization 2 * a₀ := ex
        _ = 2 ^ z.factorization 2 * a₀ := by rw [hxz]
        _ = z := ez.symm
    -- the multiplicity of `a₀` in `Ψ μ` is a sum of distinct powers of two
    have hcount : (psi μ).count a₀
        = ∑ i ∈ (μ.toFinset.filter (fun m => ordCompl[2] m = a₀)).image (fun x => x.factorization 2),
            2 ^ i := by
      rw [count_psi, Finset.sum_multiset_map_count]
      have hone : ∀ m ∈ μ.toFinset,
          μ.count m • (if ordCompl[2] m = a₀ then ordProj[2] m else 0)
            = if ordCompl[2] m = a₀ then ordProj[2] m else 0 := by
        intro m hm
        rw [Multiset.count_eq_one_of_mem hμ (Multiset.mem_toFinset.mp hm), one_smul]
      rw [Finset.sum_congr rfl hone, ← Finset.sum_filter, Finset.sum_image hinj]
    -- characterise membership of the bit `s₀`
    have hiff : s₀ ∈ Nat.bitIndices ((psi μ).count a₀) ↔ y ∈ μ := by
      rw [hcount, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, hfx⟩
        rw [Finset.mem_filter, Multiset.mem_toFinset] at hx
        have hxy : x = y := by
          have h := hyeq
          rw [← hfx] at h
          have hx2 : 2 ^ x.factorization 2 * a₀ = x := by
            rw [← hx.2]; exact Nat.ordProj_mul_ordCompl_eq_self x 2
          rwa [hx2] at h
        rw [← hxy]; exact hx.1
      · intro hyμ
        refine ⟨y, ?_, hs₀def.symm⟩
        rw [Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hyμ, ha₀.symm⟩
    simp only [hiff]

/-! ### Packaging the maps as bijections on `Nat.Partition n` -/

/-- `Ψ` as a map on partitions: distinct parts ↦ odd parts. -/
def psiP {n : ℕ} (p : Nat.Partition n) : Nat.Partition n where
  parts := psi p.parts
  parts_pos hi := psi_pos (fun _ hx => p.parts_pos hx) _ hi
  parts_sum := by rw [psi_sum]; exact p.parts_sum

/-- `Φ` as a map on partitions: odd parts ↦ distinct parts. -/
def phiP {n : ℕ} (p : Nat.Partition n) : Nat.Partition n where
  parts := phi p.parts
  parts_pos hi := phi_pos (fun _ hx => p.parts_pos hx) _ hi
  parts_sum := by rw [phi_sum]; exact p.parts_sum

/-- Membership in `odds`: all parts are odd. -/
lemma mem_odds_iff {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.odds n ↔ ∀ i ∈ p.parts, ¬ Even i := by
  simp [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter]

/-- Membership in `distincts`: the parts are pairwise distinct. -/
lemma mem_distincts_iff {n : ℕ} (p : Nat.Partition n) :
    p ∈ Nat.Partition.distincts n ↔ p.parts.Nodup := by
  simp [Nat.Partition.distincts, Finset.mem_filter]

/-- Blueprint `thm:euler_partition_bijection` (Euler's partition theorem):
the number of partitions of `n` into distinct parts equals the number into odd
parts. To be proved by the explicit constructive bijection of the blueprint. -/
theorem euler_partition (n : ℕ) :
    (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card := by
  refine Finset.card_nbij' psiP phiP ?_ ?_ ?_ ?_
  · -- `Ψ` maps distinct partitions to odd partitions
    intro p _
    rw [Finset.mem_coe, mem_odds_iff]
    exact psi_odd (fun _ hx => p.parts_pos hx)
  · -- `Φ` maps odd partitions to distinct partitions
    intro p hp
    rw [Finset.mem_coe, mem_odds_iff] at hp
    rw [Finset.mem_coe, mem_distincts_iff]
    exact phi_nodup (fun a ha => Nat.not_even_iff_odd.mp (hp a ha))
  · -- `Φ ∘ Ψ = id` on distinct partitions
    intro p hp
    rw [Finset.mem_coe, mem_distincts_iff] at hp
    apply Nat.Partition.ext
    exact phi_psi hp (fun _ hx => p.parts_pos hx)
  · -- `Ψ ∘ Φ = id` on odd partitions
    intro p hp
    rw [Finset.mem_coe, mem_odds_iff] at hp
    apply Nat.Partition.ext
    exact psi_phi (fun a ha => Nat.not_even_iff_odd.mp (hp a ha))

/-! ### Computable sanity checks (reduce under `#eval`) -/

#eval O 6                            -- 4
#eval D 6                            -- 4
#eval psi {5, 1}                     -- Ψ(5+1)     = {5, 1}
#eval phi (Multiset.replicate 6 1)   -- Φ(1^6)     = {2, 4}
#eval phi {5, 1}                     -- Φ(5+1)     = {5, 1}
#eval psi {2, 4}                     -- Ψ(4+2)     = {1, 1, 1, 1, 1, 1}

end EulerPartition
