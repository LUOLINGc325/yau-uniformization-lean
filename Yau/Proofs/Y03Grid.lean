import Yau.Blueprint.Alignment

/-! Arithmetic of the literal canonical grid used by Y03. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

variable (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ)

theorem one_le_pieces (j : ℕ) : 1 ≤ pieces Q N M hm j := by
  unfold pieces
  split
  · exact le_rfl
  · exact le_max_left _ _

theorem offset_self (j₀ : ℕ) : offset Q N M hm j₀ j₀ = 0 := by
  simp [offset]

theorem offset_succ {j₀ j : ℕ} (hj : j₀ ≤ j) :
    offset Q N M hm j₀ (j + 1) = offset Q N M hm j₀ j + pieces Q N M hm j := by
  unfold offset
  rw [show j + 1 - j₀ = (j - j₀) + 1 by omega, Finset.sum_range_succ]
  rw [Nat.add_sub_of_le hj]

theorem sub_le_offset (j₀ j : ℕ) : j - j₀ ≤ offset Q N M hm j₀ j := by
  calc
    j - j₀ = ∑ _r ∈ Finset.range (j - j₀), 1 := by simp
    _ ≤ offset Q N M hm j₀ j := by
      unfold offset
      exact Finset.sum_le_sum fun r _ => one_le_pieces Q N M hm (j₀ + r)

theorem offset_strictMonoOn (j₀ : ℕ) :
    StrictMonoOn (offset Q N M hm j₀) (Set.Ici j₀) := by
  have h : StrictMono (fun r => offset Q N M hm j₀ (j₀ + r)) := by
    apply strictMono_nat_of_lt_succ
    intro r
    rw [show j₀ + (r + 1) = (j₀ + r) + 1 by omega,
      offset_succ Q N M hm (by omega : j₀ ≤ j₀ + r)]
    have := one_le_pieces Q N M hm (j₀ + r)
    omega
  intro a ha b hb hab
  have hd : a - j₀ < b - j₀ := by simp only [Set.mem_Ici] at ha hb; omega
  simpa only [Nat.add_sub_of_le ha, Nat.add_sub_of_le hb] using h hd

theorem macroAt_set_nonempty (j₀ k : ℕ) :
    {j | j₀ ≤ j ∧ k < offset Q N M hm j₀ (j + 1)}.Nonempty := by
  refine ⟨j₀ + k, by omega, ?_⟩
  have := sub_le_offset Q N M hm j₀ (j₀ + k + 1)
  omega

theorem macroAt_mem (j₀ k : ℕ) :
    j₀ ≤ macroAt Q N M hm j₀ k ∧
      k < offset Q N M hm j₀ (macroAt Q N M hm j₀ k + 1) := by
  exact csInf_mem (macroAt_set_nonempty Q N M hm j₀ k)

theorem offset_macroAt_le (j₀ k : ℕ) :
    offset Q N M hm j₀ (macroAt Q N M hm j₀ k) ≤ k := by
  let j := macroAt Q N M hm j₀ k
  have hj : j₀ ≤ j := (macroAt_mem Q N M hm j₀ k).1
  by_cases h : j = j₀
  · simp [j, h, offset]
  · by_contra hn
    have hjpos : 0 < j := by omega
    have hmem : j - 1 ∈ {a | j₀ ≤ a ∧ k < offset Q N M hm j₀ (a + 1)} := by
      constructor
      · omega
      · simpa [Nat.sub_add_cancel hjpos] using (lt_of_not_ge hn)
    have hmin : j ≤ j - 1 := csInf_le' hmem
    omega

theorem macroAt_eq_iff {j₀ k j : ℕ} :
    macroAt Q N M hm j₀ k = j ↔
      j₀ ≤ j ∧ offset Q N M hm j₀ j ≤ k ∧ k < offset Q N M hm j₀ (j + 1) := by
  constructor
  · rintro rfl
    exact ⟨(macroAt_mem Q N M hm j₀ k).1,
      offset_macroAt_le Q N M hm j₀ k, (macroAt_mem Q N M hm j₀ k).2⟩
  · rintro ⟨hj, hlo, hhi⟩
    apply le_antisymm
    · exact csInf_le' ⟨hj, hhi⟩
    · by_contra hn
      have hlt : macroAt Q N M hm j₀ k < j := lt_of_not_ge hn
      have hbase := (macroAt_mem Q N M hm j₀ k).1
      have hmono := (offset_strictMonoOn Q N M hm j₀).monotoneOn
      have hle := hmono (by omega : j₀ ≤ macroAt Q N M hm j₀ k + 1) hj
        (by omega : macroAt Q N M hm j₀ k + 1 ≤ j)
      have := (macroAt_mem Q N M hm j₀ k).2
      omega

theorem slotAt_lt_pieces (j₀ k : ℕ) :
    slotAt Q N M hm j₀ k < pieces Q N M hm (macroAt Q N M hm j₀ k) := by
  have h := macroAt_mem Q N M hm j₀ k
  have hlo := offset_macroAt_le Q N M hm j₀ k
  rw [offset_succ Q N M hm h.1] at h
  unfold slotAt
  omega

theorem offset_add_slotAt (j₀ k : ℕ) :
    offset Q N M hm j₀ (macroAt Q N M hm j₀ k) + slotAt Q N M hm j₀ k = k := by
  exact Nat.add_sub_of_le (offset_macroAt_le Q N M hm j₀ k)

theorem macroAt_offset {j₀ j : ℕ} (hj : j₀ ≤ j) :
    macroAt Q N M hm j₀ (offset Q N M hm j₀ j) = j := by
  apply (macroAt_eq_iff Q N M hm).2
  refine ⟨hj, le_rfl, ?_⟩
  rw [offset_succ Q N M hm hj]
  have := one_le_pieces Q N M hm j
  omega

theorem gridClock_offset {j₀ j : ℕ} (hj : j₀ ≤ j) :
    gridClock Q N M hm j₀ (offset Q N M hm j₀ j) = macroClock hm j := by
  simp [gridClock, slotAt, macroAt_offset Q N M hm hj]

theorem gridClock_zero (j₀ : ℕ) :
    gridClock Q N M hm j₀ 0 = macroClock hm j₀ := by
  simpa only [offset_self] using gridClock_offset Q N M hm (le_refl j₀)

theorem macroAt_succ_eq_or (j₀ k : ℕ) :
    macroAt Q N M hm j₀ (k + 1) = macroAt Q N M hm j₀ k ∨
      macroAt Q N M hm j₀ (k + 1) = macroAt Q N M hm j₀ k + 1 := by
  let j := macroAt Q N M hm j₀ k
  have hj := macroAt_mem Q N M hm j₀ k
  have hlo := offset_macroAt_le Q N M hm j₀ k
  by_cases hi : k + 1 < offset Q N M hm j₀ (j + 1)
  · left
    exact (macroAt_eq_iff Q N M hm).2 ⟨hj.1, by omega, hi⟩
  · right
    have heq : k + 1 = offset Q N M hm j₀ (j + 1) := by dsimp [j] at hi ⊢; omega
    rw [heq]
    exact macroAt_offset Q N M hm (by dsimp [j]; omega)

theorem macroClock_pos (j : ℕ) : 0 < macroClock hm j := Real.exp_pos _

theorem macroClock_succ (j : ℕ) :
    macroClock hm (j + 1) = Real.exp hm * macroClock hm j := by
  unfold macroClock
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add, mul_comm]

theorem macroClock_strictMono (hhm : 0 < hm) : StrictMono (macroClock hm) := by
  intro i j hij
  apply Real.exp_lt_exp.2
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hhm

theorem macroClock_tendsto (hhm : 0 < hm) : Tendsto (macroClock hm) atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    (Filter.Tendsto.const_mul_atTop hhm tendsto_natCast_atTop_atTop)

theorem gridClock_mem_Ico (hhm : 0 < hm) (j₀ k : ℕ) :
    macroClock hm (macroAt Q N M hm j₀ k) ≤ gridClock Q N M hm j₀ k ∧
      gridClock Q N M hm j₀ k < macroClock hm (macroAt Q N M hm j₀ k + 1) := by
  let j := macroAt Q N M hm j₀ k
  have hp : 0 < (pieces Q N M hm j : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_pieces Q N M hm j)
  have hslot : (slotAt Q N M hm j₀ k : ℝ) < pieces Q N M hm j := by
    exact_mod_cast slotAt_lt_pieces Q N M hm j₀ k
  have hd : 0 < macroClock hm (j + 1) - macroClock hm j :=
    sub_pos.2 (macroClock_strictMono hm hhm (Nat.lt_succ_self j))
  have hfrac0 : 0 ≤ (slotAt Q N M hm j₀ k : ℝ) / pieces Q N M hm j := by positivity
  have hfrac1 : (slotAt Q N M hm j₀ k : ℝ) / pieces Q N M hm j < 1 :=
    (div_lt_one₀ hp).2 hslot
  change macroClock hm j ≤ macroClock hm j + _ ∧
    macroClock hm j + _ < macroClock hm (j + 1)
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hfrac0 hd.le)
  · nlinarith

theorem gridClock_succ_sub (j₀ k : ℕ) :
    gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k =
      (macroClock hm (macroAt Q N M hm j₀ k + 1) -
        macroClock hm (macroAt Q N M hm j₀ k)) /
          pieces Q N M hm (macroAt Q N M hm j₀ k) := by
  let j := macroAt Q N M hm j₀ k
  have hj := macroAt_mem Q N M hm j₀ k
  have hlo := offset_macroAt_le Q N M hm j₀ k
  have hslot := offset_add_slotAt Q N M hm j₀ k
  have hp : (pieces Q N M hm j : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (one_le_pieces Q N M hm j))
  rcases macroAt_succ_eq_or Q N M hm j₀ k with heq | heq
  · have hslots : slotAt Q N M hm j₀ (k + 1) = slotAt Q N M hm j₀ k + 1 := by
      unfold slotAt
      rw [heq]
      omega
    simp only [gridClock, heq, hslots, Nat.cast_add, Nat.cast_one]
    dsimp [j] at hp
    field_simp
    ring
  · have hnext : k + 1 = offset Q N M hm j₀ (j + 1) := by
      have hlowNext := offset_macroAt_le Q N M hm j₀ (k + 1)
      rw [heq] at hlowNext
      dsimp [j]
      omega
    have hlast : slotAt Q N M hm j₀ k + 1 = pieces Q N M hm j := by
      have hoff := offset_succ Q N M hm hj.1
      dsimp [j] at hnext ⊢
      omega
    have hlastR : (slotAt Q N M hm j₀ k : ℝ) + 1 = pieces Q N M hm j := by
      exact_mod_cast hlast
    rw [hnext, gridClock_offset Q N M hm (by dsimp [j]; omega)]
    change macroClock hm (j + 1) -
      (macroClock hm j + (slotAt Q N M hm j₀ k : ℝ) / pieces Q N M hm j *
        (macroClock hm (j + 1) - macroClock hm j)) = _
    dsimp only [j] at hp hlastR ⊢
    field_simp
    rw [← hlastR]
    ring

theorem gridClock_strictMono (hhm : 0 < hm) (j₀ : ℕ) :
    StrictMono (gridClock Q N M hm j₀) := by
  apply strictMono_nat_of_lt_succ
  intro k
  apply sub_pos.1
  rw [gridClock_succ_sub]
  apply div_pos
  · exact sub_pos.2 (macroClock_strictMono hm hhm (Nat.lt_succ_self _))
  · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_pieces Q N M hm _)

theorem gridClock_tendsto (hhm : 0 < hm) (j₀ : ℕ) :
    Tendsto (gridClock Q N M hm j₀) atTop atTop := by
  apply (gridClock_strictMono Q N M hm hhm j₀).monotone.tendsto_atTop_atTop_iff.2
  intro B
  obtain ⟨j, hj⟩ := (tendsto_atTop_atTop.1 (macroClock_tendsto hm hhm)) B
  refine ⟨offset Q N M hm j₀ (max j₀ j), ?_⟩
  rw [gridClock_offset Q N M hm (le_max_left _ _)]
  exact hj _ (le_max_right _ _)

theorem gridClock_step_upper (hhm : 0 < hm) (j₀ k : ℕ) :
    gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k ≤
      (Real.exp hm - 1) * gridClock Q N M hm j₀ k := by
  rw [gridClock_succ_sub]
  have hp : 1 ≤ (pieces Q N M hm (macroAt Q N M hm j₀ k) : ℝ) := by
    exact_mod_cast one_le_pieces Q N M hm _
  have hd := (macroClock_strictMono hm hhm) (Nat.lt_succ_self (macroAt Q N M hm j₀ k))
  have he : 0 ≤ Real.exp hm - 1 := sub_nonneg.2 (Real.one_le_exp hhm.le)
  calc
    _ ≤ macroClock hm (macroAt Q N M hm j₀ k + 1) -
        macroClock hm (macroAt Q N M hm j₀ k) :=
      div_le_self (sub_nonneg.2 hd.le) hp
    _ = (Real.exp hm - 1) * macroClock hm (macroAt Q N M hm j₀ k) := by
      rw [macroClock_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gridClock_mem_Ico Q N M hm hhm j₀ k).1 he

theorem pieces_sqrt_bounds (hhm : 0 < hm) {j : ℕ}
    (hsize : 1 ≤ (macroClock hm (j + 1) - macroClock hm j) /
      Real.sqrt (macroClock hm j)) :
    Real.sqrt (macroClock hm j) / 2 ≤
        (macroClock hm (j + 1) - macroClock hm j) / pieces Q N M hm j ∧
      (Regular Q N M j →
        (macroClock hm (j + 1) - macroClock hm j) / pieces Q N M hm j ≤
          Real.sqrt (macroClock hm j)) := by
  let d := macroClock hm (j + 1) - macroClock hm j
  let z := Real.sqrt (macroClock hm j)
  have hz : 0 < z := Real.sqrt_pos.2 (macroClock_pos hm j)
  have hd : 0 < d := sub_pos.2 (macroClock_strictMono hm hhm (Nat.lt_succ_self j))
  change 1 ≤ d / z at hsize
  change z / 2 ≤ d / pieces Q N M hm j ∧
    (Regular Q N M j → d / pieces Q N M hm j ≤ z)
  by_cases hbad : Bad Q N M j
  · simp only [pieces, if_pos hbad, Nat.cast_one, div_one]
    refine ⟨?_, fun hreg => False.elim (hreg hbad)⟩
    have := (le_div_iff₀ hz).1 hsize
    linarith
  · have hceil1 : 1 ≤ Nat.ceil (d / z) := Nat.one_le_ceil_iff.2 (div_pos hd hz)
    have hp : pieces Q N M hm j = Nat.ceil (d / z) := by
      simp only [pieces, if_neg hbad]
      exact max_eq_right hceil1
    have hceilPos : 0 < (Nat.ceil (d / z) : ℝ) := by exact_mod_cast (by omega : 0 < Nat.ceil (d / z))
    have hceilUpper : (Nat.ceil (d / z) : ℝ) ≤ 2 * (d / z) := by
      have := Nat.ceil_lt_add_one (le_of_lt (div_pos hd hz))
      linarith
    have hceilLower := Nat.le_ceil (d / z)
    rw [hp]
    constructor
    · apply (le_div_iff₀ hceilPos).2
      have hh := (le_div_iff₀ hz).1 (show (Nat.ceil (d / z) : ℝ) / 2 ≤ d / z by linarith)
      nlinarith
    · intro _
      apply (div_le_iff₀ hceilPos).2
      have hh := (div_le_iff₀ hz).1 hceilLower
      nlinarith

theorem macroClock_ratio (j : ℕ) :
    (macroClock hm (j + 1) - macroClock hm j) / Real.sqrt (macroClock hm j) =
      (Real.exp hm - 1) * Real.sqrt (macroClock hm j) := by
  have hpos := macroClock_pos hm j
  have hsqrt : Real.sqrt (macroClock hm j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  apply (div_eq_iff hsqrt).2
  rw [macroClock_succ]
  calc
    Real.exp hm * macroClock hm j - macroClock hm j =
        (Real.exp hm - 1) * macroClock hm j := by ring
    _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hpos.le]

theorem gridLayout_eventually (hhm : 0 < hm) :
    ∃ J : ℕ, ∀ j₀, J ≤ j₀ → GridLayout Q N M hm j₀ := by
  have ha : 0 < Real.exp hm - 1 := sub_pos.2 (Real.one_lt_exp_iff.2 hhm)
  have hlim : Tendsto (fun j => (Real.exp hm - 1) * Real.sqrt (macroClock hm j))
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha
      (Real.tendsto_sqrt_atTop.comp (macroClock_tendsto hm hhm))
  obtain ⟨J, hJ⟩ := (tendsto_atTop_atTop.1 hlim) 1
  refine ⟨J, fun j₀ hj₀ => ?_⟩
  refine ⟨gridClock_zero Q N M hm j₀, gridClock_strictMono Q N M hm hhm j₀,
    gridClock_tendsto Q N M hm hhm j₀, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(macroAt_mem Q N M hm j₀ k).1, slotAt_lt_pieces Q N M hm j₀ k,
      (offset_add_slotAt Q N M hm j₀ k).symm⟩
  · intro j hj
    exact gridClock_offset Q N M hm hj
  · refine ⟨(2 * Real.sqrt (Real.exp hm))⁻¹, 1, by positivity, zero_lt_one, ?_⟩
    intro k
    let j := macroAt Q N M hm j₀ k
    have hj : J ≤ j := hj₀.trans (macroAt_mem Q N M hm j₀ k).1
    have hsize : 1 ≤ (macroClock hm (j + 1) - macroClock hm j) /
        Real.sqrt (macroClock hm j) := by
      rw [macroClock_ratio]
      exact hJ j hj
    have hpieces := pieces_sqrt_bounds Q N M hm hhm hsize
    have hmem := gridClock_mem_Ico Q N M hm hhm j₀ k
    have hspos : 0 < gridClock Q N M hm j₀ k :=
      (macroClock_pos hm j).trans_le hmem.1
    have hsqrt : Real.sqrt (gridClock Q N M hm j₀ k) ≤
        Real.sqrt (Real.exp hm) * Real.sqrt (macroClock hm j) := by
      have hle := Real.sqrt_le_sqrt hmem.2.le
      rw [macroClock_succ, Real.sqrt_mul (Real.exp_pos hm).le] at hle
      exact hle
    refine ⟨?_, gridClock_step_upper Q N M hm hhm j₀ k, ?_⟩
    · rw [gridClock_succ_sub]
      apply le_trans _ hpieces.1
      have hexppos : 0 < Real.sqrt (Real.exp hm) := Real.sqrt_pos.2 (Real.exp_pos hm)
      apply (inv_mul_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (Real.exp hm))).2
      nlinarith
    · intro hreg
      rw [gridClock_succ_sub, one_mul]
      exact (hpieces.2 hreg).trans (Real.sqrt_le_sqrt hmem.1)

end Yau.Blueprint.Alignment.Y03Proof
