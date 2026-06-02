import Mathlib

/-!
# Euler's Partition Theorem — CHOICE-FREE formalization

Goal: prove Euler's partition theorem (odd-part partitions ≃ distinct-part
partitions of `n`) following the blueprint's explicit Φ/Ψ bijection, but with the
final results depending on NO `Classical.choice` — only `[propext, Quot.sound]`.

The `#assert_choice_free` command at the bottom is a HARD GATE: once the proofs are
sorry-free, the file only compiles if the two targets are genuinely choice-free.
-/

open Lean Elab Command in
/-- Compile-time gate: errors iff `id` depends on `Classical.choice`.
While a `sorry` remains, the decl depends on `sorryAx` (not choice) so this passes;
once sorry-free it ERRORS unless the proof is genuinely choice-free. -/
elab "#assert_choice_free " id:ident : command => do
  let name := id.getId
  let axs ← liftCoreM <| Lean.collectAxioms name
  if axs.contains ``Classical.choice then
    throwError "✗ {name} still depends on Classical.choice : {axs}"
  else
    logInfo m!"✓ {name} is choice-free : {axs}"

open Nat

namespace EulerCF

/-! ## Choice-free list/multiset infrastructure -/

/-- Count after erasing the erased element decreases by one. Choice-free. -/
theorem count_erase_self (a : ℕ) (l : List ℕ) :
    (l.erase a).count a = l.count a - 1 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    by_cases hb : b = a
    · subst hb; rw [List.erase_cons_head, List.count_cons_self]; omega
    · rw [List.erase_cons_tail (by simp [hb])]
      simp only [List.count_cons, ih]
      rw [if_neg (by simpa using hb)]; omega

/-- Count of another value is unchanged by erase. Choice-free. -/
theorem count_erase_ne (a b : ℕ) (l : List ℕ) (h : b ≠ a) :
    (l.erase a).count b = l.count b := by
  induction l with
  | nil => simp
  | cons c t ih =>
    by_cases hc : c = a
    · subst hc; rw [List.erase_cons_head, List.count_cons_of_ne (Ne.symm h)]
    · rw [List.erase_cons_tail (by simp [hc]), List.count_cons, List.count_cons, ih]

/-- A list is a permutation of its head-erased form. Choice-free. -/
theorem perm_cons_erase (a : ℕ) (l : List ℕ) (h : a ∈ l) :
    l.Perm (a :: l.erase a) := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    by_cases hb : b = a
    · subst hb; rw [List.erase_cons_head]
    · rw [List.erase_cons_tail (by simp [hb])]
      have hmem : a ∈ t := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hb
        · exact h'
      exact (List.Perm.cons b (ih hmem)).trans (List.Perm.swap a b (t.erase a))

/-- Equal counts ⟹ permutation, choice-free (for `ℕ`). -/
theorem perm_of_count : ∀ {l₁ l₂ : List ℕ}, (∀ a, l₁.count a = l₂.count a) → l₁.Perm l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    have hnil : l₂ = [] := by
      rcases l₂ with _ | ⟨b, t⟩
      · rfl
      · have hb := (h b).symm; rw [List.count_cons_self] at hb; simp at hb
    subst hnil; exact List.Perm.refl _
  | cons a t ih =>
    intro l₂ h
    have ha : a ∈ l₂ := by
      have hh := h a; rw [List.count_cons_self] at hh
      exact List.count_pos_iff.mp (by omega)
    refine (List.Perm.cons a (ih (l₂ := l₂.erase a) ?_)).trans (perm_cons_erase a l₂ ha).symm
    intro b
    by_cases hb : b = a
    · subst hb
      have hh := h b; rw [List.count_cons_self] at hh
      rw [count_erase_self]; omega
    · have hh := h b; rw [List.count_cons_of_ne (Ne.symm hb)] at hh
      rw [count_erase_ne a b l₂ hb]; exact hh

/-- Count-extensionality for multisets of `ℕ`, choice-free. -/
theorem msext {s t : Multiset ℕ} (h : ∀ a, s.count a = t.count a) : s = t := by
  induction s using Quotient.inductionOn with
  | _ l₁ =>
    induction t using Quotient.inductionOn with
    | _ l₂ =>
      apply Quotient.sound
      apply perm_of_count
      intro a
      have hh := h a
      rwa [Multiset.quot_mk_to_coe, Multiset.quot_mk_to_coe,
        Multiset.coe_count, Multiset.coe_count] at hh

/-- `Nodup` list: count is the membership indicator. Choice-free. -/
theorem nodup_count (a : ℕ) (l : List ℕ) (h : l.Nodup) :
    l.count a = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.nodup_cons] at h
    by_cases ha : a = b
    · subst ha
      rw [List.count_cons_self, List.count_eq_zero.mpr h.1, if_pos List.mem_cons_self]
    · rw [List.count_cons_of_ne (Ne.symm ha), ih h.2]
      by_cases hmem : a ∈ t
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem _ hmem)]
      · rw [if_neg hmem, if_neg (fun hc => (List.mem_cons.mp hc).elim ha hmem)]

/-- Membership in `List.dedup` (choice-free version). -/
theorem mem_dedup (a : ℕ) (l : List ℕ) : a ∈ l.dedup ↔ a ∈ l := by
  constructor
  · intro h; exact (List.dedup_sublist l).mem h
  · intro h
    induction l with
    | nil => simp at h
    | cons b t ih =>
      unfold List.dedup at *
      by_cases hb : ∀ a' ∈ List.pwFilter (· ≠ ·) t, b ≠ a'
      · rw [List.pwFilter_cons_of_pos hb]
        rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h')
      · rw [List.pwFilter_cons_of_neg hb]
        rcases List.mem_cons.mp h with rfl | h'
        · by_cases haL : a ∈ List.pwFilter (· ≠ ·) t
          · exact haL
          · exfalso; apply hb; intro a' ha' heq; subst heq; exact haL ha'
        · exact ih h'

/-- Count in `List.dedup` (choice-free version). -/
theorem count_dedup (a : ℕ) (l : List ℕ) :
    l.dedup.count a = if a ∈ l then 1 else 0 := by
  rw [nodup_count a l.dedup (List.nodup_dedup l)]
  by_cases h : a ∈ l
  · rw [if_pos h, if_pos ((mem_dedup a l).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((mem_dedup a l).mp hc))]

/-- `List.dedup` respects permutations (choice-free). -/
theorem myperm_dedup {L1 L2 : List ℕ} (h : L1.Perm L2) : L1.dedup.Perm L2.dedup := by
  apply perm_of_count
  intro a
  rw [count_dedup, count_dedup]
  by_cases hm : a ∈ L1
  · rw [if_pos hm, if_pos (h.mem_iff.mp hm)]
  · rw [if_neg hm, if_neg (fun hc => hm (h.mem_iff.mpr hc))]

/-- Choice-free `Multiset.dedup` (Mathlib's pulls `Classical.choice` in its
well-definedness proof). -/
def mdedup (s : Multiset ℕ) : Multiset ℕ :=
  Quotient.liftOn s (fun L => (↑(L.dedup) : Multiset ℕ))
    (fun _ _ h => Quotient.sound (myperm_dedup h))

theorem mdedup_coe (L : List ℕ) : mdedup (↑L) = (↑(L.dedup) : Multiset ℕ) := rfl

/-- Sum of a power-of-two list over `bitIndices`. Choice-free reproof of
`Nat.sum_map_two_pow_bitIndices`. -/
theorem sum_bitIndices (m : ℕ) : ((Nat.bitIndices m).map (fun r => 2 ^ r)).sum = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hcomp : ((fun r => 2 ^ r) ∘ fun x => x + 1) = (fun r => 2 * 2 ^ r) := by
        funext r; rw [Function.comp_apply, pow_succ]; ring
      by_cases he : m % 2 = 0
      · obtain ⟨k, hk_lt, hm2⟩ : ∃ k, k < m ∧ m = 2 * k := ⟨m / 2, by omega, by omega⟩
        rw [hm2, Nat.bitIndices_two_mul, List.map_map, hcomp, List.sum_map_mul_left, ih k hk_lt]
      · obtain ⟨k, hk_lt, hm2⟩ : ∃ k, k < m ∧ m = 2 * k + 1 := ⟨m / 2, by omega, by omega⟩
        rw [hm2, Nat.bitIndices_two_mul_add_one, List.map_cons, List.sum_cons, List.map_map,
          hcomp, List.sum_map_mul_left, ih k hk_lt, pow_zero]
        omega

/-! ## Choice-free 2-adic valuation and odd part -/

/-- 2-adic valuation, by well-founded recursion (choice-free). -/
def v2 : ℕ → ℕ
  | 0 => 0
  | (n + 1) => if (n + 1) % 2 = 0 then v2 ((n + 1) / 2) + 1 else 0
decreasing_by omega

/-- Odd part, by well-founded recursion (choice-free). -/
def oddPart : ℕ → ℕ
  | 0 => 0
  | (n + 1) => if (n + 1) % 2 = 0 then oddPart ((n + 1) / 2) else (n + 1)
decreasing_by omega

theorem v2_zero : v2 0 = 0 := by rw [v2]
theorem oddPart_zero : oddPart 0 = 0 := by rw [oddPart]

theorem v2_even {x : ℕ} (hx : 0 < x) (he : x % 2 = 0) : v2 x = v2 (x / 2) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [v2]; rw [if_pos he]

theorem v2_odd_eq {x : ℕ} (ho : x % 2 = 1) : v2 x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [v2]; rw [if_neg (by omega)]

theorem oddPart_even {x : ℕ} (hx : 0 < x) (he : x % 2 = 0) : oddPart x = oddPart (x / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [oddPart]; rw [if_pos he]

theorem oddPart_odd_eq {x : ℕ} (ho : x % 2 = 1) : oddPart x = x := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [oddPart]; rw [if_neg (by omega)]

theorem odd_of_mod {n : ℕ} (h : n % 2 = 1) : Odd n := ⟨n / 2, by omega⟩
theorem mod_of_odd {n : ℕ} (h : Odd n) : n % 2 = 1 := by obtain ⟨m, rfl⟩ := h; omega

/-- The defining factorization `2 ^ v2 x * oddPart x = x`. -/
theorem two_pow_v2_mul_oddPart (x : ℕ) : 2 ^ v2 x * oddPart x = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [oddPart_zero, v2_zero]
    · by_cases he : x % 2 = 0
      · rw [v2_even hx he, oddPart_even hx he, pow_succ]
        have hlt : x / 2 < x := by omega
        rw [mul_comm (2 ^ v2 (x / 2)) 2, mul_assoc, ih (x / 2) hlt]; omega
      · have ho : x % 2 = 1 := by omega
        rw [v2_odd_eq ho, oddPart_odd_eq ho, pow_zero, one_mul]

theorem oddPart_odd (x : ℕ) (hx : 0 < x) : Odd (oddPart x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases he : x % 2 = 0
    · rw [oddPart_even hx he]
      have hlt : x / 2 < x := by omega
      exact ih (x / 2) hlt (by omega)
    · have ho : x % 2 = 1 := by omega
      rw [oddPart_odd_eq ho]; exact odd_of_mod ho

theorem oddPart_pos (x : ℕ) (hx : 0 < x) : 0 < oddPart x := by
  have := mod_of_odd (oddPart_odd x hx); omega

theorem oddPart_two_pow_mul {a : ℕ} (ha : a % 2 = 1) (r : ℕ) : oddPart (2 ^ r * a) = a := by
  induction r with
  | zero => rw [pow_zero, one_mul, oddPart_odd_eq ha]
  | succ r ih =>
    have hapos : 0 < a := by omega
    have hpos : 0 < 2 ^ (r + 1) * a := Nat.mul_pos (Nat.two_pow_pos (r + 1)) hapos
    have hsplit : 2 ^ (r + 1) * a = 2 * (2 ^ r * a) := by rw [pow_succ]; ring
    have he : (2 ^ (r + 1) * a) % 2 = 0 := by omega
    have hdiv : (2 ^ (r + 1) * a) / 2 = 2 ^ r * a := by omega
    rw [oddPart_even hpos he, hdiv, ih]

theorem v2_two_pow_mul {a : ℕ} (ha : a % 2 = 1) (r : ℕ) : v2 (2 ^ r * a) = r := by
  induction r with
  | zero => rw [pow_zero, one_mul, v2_odd_eq ha]
  | succ r ih =>
    have hapos : 0 < a := by omega
    have hpos : 0 < 2 ^ (r + 1) * a := Nat.mul_pos (Nat.two_pow_pos (r + 1)) hapos
    have hsplit : 2 ^ (r + 1) * a = 2 * (2 ^ r * a) := by rw [pow_succ]; ring
    have he : (2 ^ (r + 1) * a) % 2 = 0 := by omega
    have hdiv : (2 ^ (r + 1) * a) / 2 = 2 ^ r * a := by omega
    rw [v2_even hpos he, hdiv, ih]

/-! ## The targets -/

/-- A partition of `n` into **odd** parts. -/
def OddPartition (n : ℕ) : Type :=
  { l : Multiset ℕ // (∀ i ∈ l, 0 < i) ∧ l.sum = n ∧ ∀ i ∈ l, Odd i }

/-- A partition of `n` into **distinct** parts. -/
def DistinctPartition (n : ℕ) : Type :=
  { l : Multiset ℕ // (∀ i ∈ l, 0 < i) ∧ l.sum = n ∧ l.Nodup }

/-- Blueprint `lem:two_adic_odd_factorization`, proved CHOICE-FREE. -/
theorem two_adic_odd_factorization {x : ℕ} (hx : 0 < x) :
    ∃! ra : ℕ × ℕ, Odd ra.2 ∧ x = 2 ^ ra.1 * ra.2 := by
  refine ⟨(v2 x, oddPart x), ⟨oddPart_odd x hx, (two_pow_v2_mul_oddPart x).symm⟩, ?_⟩
  rintro ⟨s, b⟩ ⟨hb, hxb⟩
  have hbmod : b % 2 = 1 := mod_of_odd hb
  have hb_op : oddPart x = b := by rw [hxb]; exact oddPart_two_pow_mul hbmod s
  have hb_v2 : v2 x = s := by rw [hxb]; exact v2_two_pow_mul hbmod s
  simp only [Prod.mk.injEq]
  exact ⟨hb_v2.symm, hb_op.symm⟩

/-! ## More choice-free arithmetic / bit infrastructure -/

theorem two_pow_lt {r s : ℕ} (h : r < s) : 2 ^ r < 2 ^ s := by
  have hsplit : 2 ^ s = 2 ^ r * 2 ^ (s - r) := by rw [← pow_add]; congr 1; omega
  have h1 : 1 < 2 ^ (s - r) := Nat.one_lt_two_pow (by omega)
  have h2 : 0 < 2 ^ r := Nat.two_pow_pos r
  have hle : 2 ^ r * 2 ≤ 2 ^ r * 2 ^ (s - r) := Nat.mul_le_mul_left _ (by omega)
  rw [hsplit]; omega

theorem two_pow_inj {r s : ℕ} (h : 2 ^ r = 2 ^ s) : r = s := by
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (two_pow_lt hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (two_pow_lt hgt))

theorem succ_inj : Function.Injective (fun x : ℕ => x + 1) := by
  intro a b hab; exact Nat.add_right_cancel hab

theorem bitIndices_nodup : ∀ m, (Nat.bitIndices m).Nodup := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.bitIndices_zero]; exact List.nodup_nil
    · by_cases he : m % 2 = 0
      · obtain ⟨k, hk, hm2⟩ : ∃ k, k < m ∧ m = 2 * k := ⟨m / 2, by omega, by omega⟩
        rw [hm2, Nat.bitIndices_two_mul]
        exact (ih k hk).map succ_inj
      · obtain ⟨k, hk, hm2⟩ : ∃ k, k < m ∧ m = 2 * k + 1 := ⟨m / 2, by omega, by omega⟩
        rw [hm2, Nat.bitIndices_two_mul_add_one, List.nodup_cons]
        refine ⟨?_, (ih k hk).map succ_inj⟩
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨x, _, hx⟩ := hmem; omega

/-- testBit of `2^a + M` at a higher bit `e > a`, no carry since bit `a` of `M` is `0`. -/
theorem testBit_two_pow_add_high :
    ∀ (a : ℕ) (M e : ℕ), M.testBit a = false → a < e → (2 ^ a + M).testBit e = M.testBit e := by
  intro a
  induction a with
  | zero =>
    intro M e hM he
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [pow_zero, Nat.testBit_succ, Nat.testBit_succ]
    have hMeven : M % 2 = 0 := by
      have := hM; rw [Nat.testBit_zero] at this; simp at this; omega
    congr 1; omega
  | succ a ih =>
    intro M e hM he
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.testBit_succ, Nat.testBit_succ]
    have hsplit : (2 ^ (a + 1) + M) / 2 = 2 ^ a + M / 2 := by
      have : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
      omega
    rw [hsplit]
    apply ih
    · rw [Nat.testBit_succ] at hM; exact hM
    · omega

/-- Adding a fresh power of two inserts its exponent into `bitIndices`. -/
theorem bitIndices_two_pow_add (a M e : ℕ) (ha : M.testBit a = false) :
    e ∈ Nat.bitIndices (2 ^ a + M) ↔ e = a ∨ e ∈ Nat.bitIndices M := by
  rw [Nat.mem_bitIndices, Nat.mem_bitIndices]
  rcases lt_trichotomy e a with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]
    constructor
    · exact fun hb => Or.inr hb
    · rintro (rfl | hb)
      · exact absurd h (lt_irrefl _)
      · exact hb
  · rw [Nat.testBit_two_pow_add_eq, ha]; simp
  · rw [testBit_two_pow_add_high a M e ha h]
    constructor
    · exact fun hb => Or.inr hb
    · rintro (rfl | hb)
      · exact absurd h (lt_irrefl _)
      · exact hb

/-! ## Multiset count / dedup helpers (choice-free) -/

theorem count_eq_zero_ms (a : ℕ) (s : Multiset ℕ) (h : a ∉ s) : s.count a = 0 := by
  by_contra hne
  exact h (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))

theorem count_nodup_ms (s : Multiset ℕ) (hs : s.Nodup) (y : ℕ) :
    s.count y = if y ∈ s then 1 else 0 := by
  have hle : s.count y ≤ 1 := (Multiset.nodup_iff_count_le_one.mp hs) y
  by_cases hm : y ∈ s
  · rw [if_pos hm]
    have hpos : 0 < s.count y := Multiset.count_pos.mpr hm
    omega
  · rw [if_neg hm]; exact count_eq_zero_ms y s hm

theorem mem_dedup_ms (a : ℕ) (s : Multiset ℕ) : a ∈ mdedup s ↔ a ∈ s := by
  induction s using Quotient.inductionOn with
  | _ l =>
    show a ∈ mdedup (↑l : Multiset ℕ) ↔ a ∈ (↑l : Multiset ℕ)
    rw [mdedup_coe, Multiset.mem_coe, Multiset.mem_coe]
    exact mem_dedup a l

theorem count_dedup_ms (a : ℕ) (s : Multiset ℕ) :
    (mdedup s).count a = if a ∈ s then 1 else 0 := by
  induction s using Quotient.inductionOn with
  | _ l =>
    show (mdedup (↑l : Multiset ℕ)).count a = if a ∈ (↑l : Multiset ℕ) then 1 else 0
    rw [mdedup_coe, Multiset.coe_count, count_dedup a l]
    by_cases h : a ∈ l
    · rw [if_pos h, if_pos (Multiset.mem_coe.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (Multiset.mem_coe.mp hc))]

theorem nodup_dedup_ms (s : Multiset ℕ) : (mdedup s).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [count_dedup_ms a s]
  split <;> omega

/-- Sum of an indicator over a `Nodup` multiset picks out the single matching value. -/
theorem sum_map_ite_eq : ∀ (s : Multiset ℕ), s.Nodup → ∀ (c : ℕ) (g : ℕ → ℕ),
    (s.map (fun a => if a = c then g a else 0)).sum = if c ∈ s then g c else 0 := by
  intro s
  induction s using Multiset.induction with
  | empty =>
    intro _ c g; rw [Multiset.map_zero, Multiset.sum_zero, if_neg (Multiset.notMem_zero c)]
  | cons a t ih =>
    intro hs c g
    rw [Multiset.nodup_cons] at hs
    rw [Multiset.map_cons, Multiset.sum_cons, ih hs.2 c g]
    by_cases hac : a = c
    · subst hac
      rw [if_pos rfl, if_pos (Multiset.mem_cons_self a t), if_neg hs.1, add_zero]
    · rw [if_neg hac]
      by_cases hct : c ∈ t
      · rw [if_pos hct, if_pos (Multiset.mem_cons_of_mem hct), zero_add]
      · rw [if_neg hct,
          if_neg (fun hh => (Multiset.mem_cons.mp hh).elim (fun he => hac he.symm) hct), add_zero]

/-! ### `mflatMap`: choice-free `Multiset.bind` replacement via `List.flatMap`

`Multiset.bind`/`Multiset.sum` over multisets-of-multisets pulls a choice-tainted
`AddCommMonoid (Multiset ℕ)` instance, so we build our own join from `List.flatMap`
(whose per-element function returns a `List`), lifted across the quotient. -/

def mflatMap (s : Multiset ℕ) (f : ℕ → List ℕ) : Multiset ℕ :=
  Quotient.liftOn s (fun L => (↑(L.flatMap f) : Multiset ℕ))
    (fun _ _ h => Quotient.sound (h.flatMap_right f))

theorem mflatMap_coe (L : List ℕ) (f : ℕ → List ℕ) :
    mflatMap (↑L) f = (↑(L.flatMap f) : Multiset ℕ) := rfl

theorem mflatMap_zero (f : ℕ → List ℕ) : mflatMap 0 f = 0 := rfl

theorem mflatMap_cons (a : ℕ) (s : Multiset ℕ) (f : ℕ → List ℕ) :
    mflatMap (a ::ₘ s) f = (↑(f a) : Multiset ℕ) + mflatMap s f := by
  induction s using Quotient.inductionOn with
  | _ L =>
    show mflatMap (a ::ₘ (↑L : Multiset ℕ)) f = (↑(f a) : Multiset ℕ) + (↑(L.flatMap f) : Multiset ℕ)
    rw [show a ::ₘ (↑L : Multiset ℕ) = (↑(a :: L) : Multiset ℕ) from rfl, mflatMap_coe,
      List.flatMap_cons, Multiset.coe_add]

theorem count_mflatMap (s : Multiset ℕ) (f : ℕ → List ℕ) (c : ℕ) :
    (mflatMap s f).count c = (s.map (fun a => List.count c (f a))).sum := by
  induction s using Quotient.inductionOn with
  | _ L =>
    show ((↑(L.flatMap f) : Multiset ℕ)).count c
        = ((↑L : Multiset ℕ).map (fun a => List.count c (f a))).sum
    rw [Multiset.coe_count, List.count_flatMap, Multiset.map_coe, Multiset.sum_coe]
    rfl

theorem sum_mflatMap (s : Multiset ℕ) (f : ℕ → List ℕ) :
    (mflatMap s f).sum = (s.map (fun a => (f a).sum)).sum := by
  induction s using Quotient.inductionOn with
  | _ L =>
    show ((↑(L.flatMap f) : Multiset ℕ)).sum = ((↑L : Multiset ℕ).map (fun a => (f a).sum)).sum
    rw [Multiset.sum_coe, Multiset.map_coe, Multiset.sum_coe]
    induction L with
    | nil => simp
    | cons a t ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem mapsum_mflatMap (s : Multiset ℕ) (f : ℕ → List ℕ) (g : ℕ → ℕ) :
    ((mflatMap s f).map g).sum = (s.map (fun a => ((f a).map g).sum)).sum := by
  induction s using Quotient.inductionOn with
  | _ L =>
    show (((↑(L.flatMap f) : Multiset ℕ)).map g).sum
        = ((↑L : Multiset ℕ).map (fun a => ((f a).map g).sum)).sum
    rw [Multiset.map_coe, Multiset.sum_coe, Multiset.map_coe, Multiset.sum_coe]
    induction L with
    | nil => simp
    | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem mem_mflatMap {b : ℕ} (s : Multiset ℕ) (f : ℕ → List ℕ) :
    b ∈ mflatMap s f ↔ ∃ a ∈ s, b ∈ f a := by
  induction s using Quotient.inductionOn with
  | _ L =>
    show b ∈ (↑(L.flatMap f) : Multiset ℕ) ↔ ∃ a ∈ (↑L : Multiset ℕ), b ∈ f a
    rw [Multiset.mem_coe, List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hb⟩; exact ⟨a, Multiset.mem_coe.mpr ha, hb⟩
    · rintro ⟨a, ha, hb⟩; exact ⟨a, Multiset.mem_coe.mp ha, hb⟩

/-! ## The maps Φ (phi) and Ψ (psi) -/

/-- Ψ: replace each part `x` by `2 ^ v2 x` copies of `oddPart x`. -/
def psi (μ : Multiset ℕ) : Multiset ℕ :=
  mflatMap μ fun x => List.replicate (2 ^ v2 x) (oddPart x)

/-- Φ: for each distinct part `a`, emit `2 ^ r * a` for the set bits `r` of its multiplicity. -/
def phi (l : Multiset ℕ) : Multiset ℕ :=
  mflatMap (mdedup l) fun a => (Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a

theorem psi_def (μ : Multiset ℕ) :
    psi μ = mflatMap μ fun x => List.replicate (2 ^ v2 x) (oddPart x) := rfl

theorem phi_def (l : Multiset ℕ) :
    phi l = mflatMap (mdedup l) fun a => (Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a := rfl

/-! ### Ψ facts -/

theorem count_psi (μ : Multiset ℕ) (c : ℕ) :
    (psi μ).count c = (μ.map (fun x => if oddPart x = c then 2 ^ v2 x else 0)).sum := by
  rw [psi_def, count_mflatMap]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro x _
  simp only [List.count_replicate, beq_iff_eq]

theorem psi_sum (μ : Multiset ℕ) : (psi μ).sum = μ.sum := by
  rw [psi_def, sum_mflatMap]
  have step : μ.map (fun x => (List.replicate (2 ^ v2 x) (oddPart x)).sum)
      = μ.map (fun x => x) := by
    apply Multiset.map_congr rfl
    intro x _
    rw [List.sum_replicate, smul_eq_mul, two_pow_v2_mul_oddPart]
  rw [step, Multiset.map_id']

theorem psi_pos {μ : Multiset ℕ} (hpos : ∀ x ∈ μ, 0 < x) : ∀ a ∈ psi μ, 0 < a := by
  intro a ha
  rw [psi_def, mem_mflatMap] at ha
  obtain ⟨x, hx, ha⟩ := ha
  rw [List.mem_replicate] at ha
  obtain ⟨_, rfl⟩ := ha
  exact oddPart_pos x (hpos x hx)

theorem psi_mod {μ : Multiset ℕ} (hpos : ∀ x ∈ μ, 0 < x) : ∀ a ∈ psi μ, a % 2 = 1 := by
  intro a ha
  rw [psi_def, mem_mflatMap] at ha
  obtain ⟨x, hx, ha⟩ := ha
  rw [List.mem_replicate] at ha
  obtain ⟨_, rfl⟩ := ha
  exact mod_of_odd (oddPart_odd x (hpos x hx))

/-- Count of a positive value in one Φ-block, for an odd base `a`. -/
theorem count_oddBlock {a : ℕ} (ha : a % 2 = 1) (m : ℕ) {y : ℕ} (hy : 0 < y) :
    List.count y ((Nat.bitIndices m).map fun r => 2 ^ r * a)
      = if a = oddPart y then (if v2 y ∈ Nat.bitIndices m then 1 else 0) else 0 := by
  have hapos : 0 < a := by omega
  have hinj : Function.Injective (fun r => 2 ^ r * a) := by
    intro r s hrs
    exact two_pow_inj (Nat.eq_of_mul_eq_mul_right hapos hrs)
  have hnodup : ((Nat.bitIndices m).map fun r => 2 ^ r * a).Nodup := (bitIndices_nodup m).map hinj
  have hmem : y ∈ ((Nat.bitIndices m).map fun r => 2 ^ r * a)
      ↔ (a = oddPart y ∧ v2 y ∈ Nat.bitIndices m) := by
    rw [List.mem_map]
    constructor
    · rintro ⟨r, hr, hry⟩
      have ho := oddPart_two_pow_mul ha r
      have hv := v2_two_pow_mul ha r
      rw [hry] at ho hv
      exact ⟨ho.symm, by rw [hv]; exact hr⟩
    · rintro ⟨hP, hQ⟩
      exact ⟨v2 y, hQ, by rw [hP]; exact two_pow_v2_mul_oddPart y⟩
  rw [nodup_count y _ hnodup]
  by_cases hP : a = oddPart y
  · by_cases hQ : v2 y ∈ Nat.bitIndices m
    · rw [if_pos (hmem.mpr ⟨hP, hQ⟩), if_pos hP, if_pos hQ]
    · rw [if_neg (fun hc => hQ (hmem.mp hc).2), if_pos hP, if_neg hQ]
  · rw [if_neg (fun hc => hP (hmem.mp hc).1), if_neg hP]

/-! ### Φ facts -/

theorem count_phi {l : Multiset ℕ} (hl : ∀ a ∈ l, a % 2 = 1) {y : ℕ} (hy : 0 < y) :
    (phi l).count y = if v2 y ∈ Nat.bitIndices (l.count (oddPart y)) then 1 else 0 := by
  rw [phi_def, count_mflatMap]
  have step : (mdedup l).map (fun a =>
        List.count y ((Nat.bitIndices (l.count a)).map fun r => 2 ^ r * a))
      = (mdedup l).map (fun a =>
        if a = oddPart y then (if v2 y ∈ Nat.bitIndices (l.count a) then 1 else 0) else 0) := by
    apply Multiset.map_congr rfl
    intro a ha
    exact count_oddBlock (hl a ((mem_dedup_ms a l).mp ha)) (l.count a) hy
  rw [step, sum_map_ite_eq (mdedup l) (nodup_dedup_ms l) (oddPart y)
        (fun a => if v2 y ∈ Nat.bitIndices (l.count a) then 1 else 0)]
  by_cases hmem : oddPart y ∈ mdedup l
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    have hz : l.count (oddPart y) = 0 :=
      count_eq_zero_ms _ l (fun hh => hmem ((mem_dedup_ms _ l).mpr hh))
    rw [hz, Nat.bitIndices_zero, if_neg (by simp)]

theorem l_eq_group (l : Multiset ℕ) :
    l = mflatMap (mdedup l) (fun a => List.replicate (l.count a) a) := by
  apply msext
  intro c
  rw [count_mflatMap]
  have step : (mdedup l).map (fun a => List.count c (List.replicate (l.count a) a))
      = (mdedup l).map (fun a => if a = c then l.count a else 0) := by
    apply Multiset.map_congr rfl
    intro a _
    simp only [List.count_replicate, beq_iff_eq]
  rw [step, sum_map_ite_eq (mdedup l) (nodup_dedup_ms l) c (fun a => l.count a)]
  by_cases hc : c ∈ mdedup l
  · rw [if_pos hc]
  · rw [if_neg hc]
    exact count_eq_zero_ms c l (fun hh => hc ((mem_dedup_ms c l).mpr hh))

theorem support_sum (l : Multiset ℕ) :
    ((mdedup l).map (fun a => l.count a * a)).sum = l.sum := by
  conv_rhs => rw [l_eq_group l]
  rw [sum_mflatMap]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  rw [List.sum_replicate, smul_eq_mul]

theorem phi_sum (l : Multiset ℕ) : (phi l).sum = l.sum := by
  rw [phi_def, sum_mflatMap]
  have step : (mdedup l).map (fun a =>
        ((Nat.bitIndices (l.count a)).map (fun r => 2 ^ r * a)).sum)
      = (mdedup l).map (fun a => l.count a * a) := by
    apply Multiset.map_congr rfl
    intro a _
    rw [List.sum_map_mul_right, sum_bitIndices]
  rw [step, support_sum]

theorem phi_pos {l : Multiset ℕ} (hpos : ∀ a ∈ l, 0 < a) : ∀ y ∈ phi l, 0 < y := by
  intro y hy
  rw [phi_def, mem_mflatMap] at hy
  obtain ⟨a, ha, hy⟩ := hy
  rw [List.mem_map] at hy
  obtain ⟨r, _, rfl⟩ := hy
  exact Nat.mul_pos (Nat.two_pow_pos r) (hpos a ((mem_dedup_ms a l).mp ha))

theorem phi_nodup {l : Multiset ℕ} (hl : ∀ a ∈ l, a % 2 = 1) (hpos : ∀ a ∈ l, 0 < a) :
    (phi l).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [count_eq_zero_ms 0 (phi l) (fun h => absurd (phi_pos hpos 0 h) (lt_irrefl 0))]; omega
  · rw [count_phi hl hy]; split <;> omega

/-! ### Ψ ∘ Φ = id -/

/-- Summing Ψ's weight over one Φ-block recovers the multiplicity (or `0`). -/
theorem sum_map_G_block {a : ℕ} (ha : a % 2 = 1) (m c : ℕ) :
    (((Nat.bitIndices m).map (fun r => 2 ^ r * a)).map
        (fun x => if oddPart x = c then 2 ^ v2 x else 0)).sum = if a = c then m else 0 := by
  rw [List.map_map]
  by_cases h : a = c
  · subst h
    have hcong : ((fun x => if oddPart x = a then 2 ^ v2 x else 0) ∘ fun r => 2 ^ r * a)
        = (fun r => 2 ^ r) := by
      funext r
      rw [Function.comp_apply, oddPart_two_pow_mul ha r, if_pos rfl, v2_two_pow_mul ha r]
    rw [hcong, sum_bitIndices, if_pos rfl]
  · have hcong : ((fun x => if oddPart x = c then 2 ^ v2 x else 0) ∘ fun r => 2 ^ r * a)
        = (fun _ => 0) := by
      funext r
      rw [Function.comp_apply, oddPart_two_pow_mul ha r, if_neg h]
    rw [hcong, if_neg h]
    exact List.sum_eq_zero (by intro x hx; rw [List.mem_map] at hx; obtain ⟨r, _, hr⟩ := hx; exact hr.symm)

theorem psi_phi {l : Multiset ℕ} (hl : ∀ a ∈ l, a % 2 = 1) : psi (phi l) = l := by
  apply msext
  intro c
  rw [count_psi, phi_def, mapsum_mflatMap]
  have step : (mdedup l).map (fun a =>
        (((Nat.bitIndices (l.count a)).map (fun r => 2 ^ r * a)).map
          (fun x => if oddPart x = c then 2 ^ v2 x else 0)).sum)
      = (mdedup l).map (fun a => if a = c then l.count a else 0) := by
    apply Multiset.map_congr rfl
    intro a ha
    exact sum_map_G_block (hl a ((mem_dedup_ms a l).mp ha)) (l.count a) c
  rw [step, sum_map_ite_eq (mdedup l) (nodup_dedup_ms l) c (fun a => l.count a)]
  by_cases hc : c ∈ mdedup l
  · rw [if_pos hc]
  · rw [if_neg hc]
    exact (count_eq_zero_ms c l (fun hh => hc ((mem_dedup_ms c l).mpr hh))).symm

/-! ### Φ ∘ Ψ = id -/

/-- The key multiplicity/binary bookkeeping: bit `v2 y` of the multiplicity of `oddPart y`
in `Ψ μ` is set iff `y` is a part of the (distinct) `μ`. -/
theorem psi_count_bit : ∀ (μ : Multiset ℕ), μ.Nodup → (∀ x ∈ μ, 0 < x) →
    ∀ y, 0 < y → (v2 y ∈ Nat.bitIndices ((psi μ).count (oddPart y)) ↔ y ∈ μ) := by
  intro μ
  induction μ using Multiset.induction with
  | empty =>
    intro _ _ y hy
    rw [psi_def, mflatMap_zero, Multiset.count_zero, Nat.bitIndices_zero]
    simp
  | cons c μ' ih =>
    intro hnd hpos y hy
    rw [Multiset.nodup_cons] at hnd
    have hpos' : ∀ x ∈ μ', 0 < x := fun x hx => hpos x (Multiset.mem_cons_of_mem hx)
    have hcpos : 0 < c := hpos c (Multiset.mem_cons_self c μ')
    have hcount : (psi (c ::ₘ μ')).count (oddPart y)
        = (if oddPart c = oddPart y then 2 ^ v2 c else 0) + (psi μ').count (oddPart y) := by
      rw [psi_def, mflatMap_cons, Multiset.count_add]
      congr 1
      rw [Multiset.coe_count]
      simp only [List.count_replicate, beq_iff_eq]
    rw [hcount]
    by_cases hoc : oddPart c = oddPart y
    · rw [if_pos hoc]
      have hbit : Nat.testBit ((psi μ').count (oddPart y)) (v2 c) = false := by
        have key := ih hnd.2 hpos' c hcpos
        rw [hoc, Nat.mem_bitIndices] at key
        by_contra hcontra
        rw [Bool.not_eq_false] at hcontra
        exact hnd.1 (key.mp hcontra)
      rw [bitIndices_two_pow_add (v2 c) _ (v2 y) hbit, ih hnd.2 hpos' y hy, Multiset.mem_cons]
      constructor
      · rintro (h | h)
        · left
          have hyy : y = 2 ^ v2 y * oddPart y := (two_pow_v2_mul_oddPart y).symm
          rw [h, ← hoc, two_pow_v2_mul_oddPart] at hyy
          exact hyy
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h
    · rw [if_neg hoc, zero_add, ih hnd.2 hpos' y hy, Multiset.mem_cons]
      constructor
      · intro h; exact Or.inr h
      · rintro (rfl | h)
        · exact absurd rfl hoc
        · exact h

theorem phi_psi {μ : Multiset ℕ} (hnd : μ.Nodup) (hpos : ∀ x ∈ μ, 0 < x) : phi (psi μ) = μ := by
  have hodd : ∀ a ∈ psi μ, a % 2 = 1 := psi_mod hpos
  apply msext
  intro y
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · rw [count_eq_zero_ms 0 (phi (psi μ))
        (fun h => absurd (phi_pos (psi_pos hpos) 0 h) (lt_irrefl 0)),
      count_eq_zero_ms 0 μ (fun h => absurd (hpos 0 h) (lt_irrefl 0))]
  · rw [count_phi hodd hy, count_nodup_ms μ hnd y]
    by_cases hym : y ∈ μ
    · rw [if_pos hym, if_pos ((psi_count_bit μ hnd hpos y hy).mpr hym)]
    · rw [if_neg hym, if_neg (fun hc => hym ((psi_count_bit μ hnd hpos y hy).mp hc))]

/-- Euler's partition theorem as the EXPLICIT bijection of the blueprint (Φ/Ψ). -/
def euler_equiv (n : ℕ) : OddPartition n ≃ DistinctPartition n where
  toFun p := ⟨phi p.1,
    phi_pos p.2.1,
    by rw [phi_sum]; exact p.2.2.1,
    phi_nodup (fun a ha => mod_of_odd (p.2.2.2 a ha)) p.2.1⟩
  invFun q := ⟨psi q.1,
    psi_pos q.2.1,
    by rw [psi_sum]; exact q.2.2.1,
    fun a ha => odd_of_mod (psi_mod q.2.1 a ha)⟩
  left_inv p := by
    apply Subtype.ext
    exact psi_phi (fun a ha => mod_of_odd (p.2.2.2 a ha))
  right_inv q := by
    apply Subtype.ext
    exact phi_psi q.2.2.2 q.2.1

end EulerCF

#assert_choice_free EulerCF.two_adic_odd_factorization
#assert_choice_free EulerCF.euler_equiv
