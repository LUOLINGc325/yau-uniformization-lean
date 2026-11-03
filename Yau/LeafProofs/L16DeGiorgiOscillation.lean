import Yau.LeafProofs.L16DeGiorgiOscillationScaling

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

def dgOscDyadicScale (j : ℕ) : ℝ := 2^(j+1)
def dgOscDyadicValue (j : ℕ) (r : ℝ) : ℝ := dgOscDyadicScale j*r-(dgOscDyadicScale j-1)
def dgOscDyadicBand {n : ℕ} (u : Point n → ℝ) (j : ℕ) : Set (Point n) :=
  dgMiddleCylinder n ∩ {p | 0 < dgOscDyadicValue j (u p) ∧ dgOscDyadicValue j (u p) < 1/2}

theorem dgOscDyadicScale_pos (j : ℕ) : 0 < dgOscDyadicScale j := pow_pos (by norm_num) _
theorem dgOscDyadicScale_two_le (j : ℕ) : 2 ≤ dgOscDyadicScale j := by
  simpa only [dgOscDyadicScale,pow_one] using (show (2:ℝ)^1 ≤ 2^(j+1) from pow_le_pow_right₀ (by norm_num) (by omega))

theorem dgOscDyadicScale_double_le {j k : ℕ} (hjk : j < k) :
    2*dgOscDyadicScale j ≤ dgOscDyadicScale k := by
  have hh : (2:ℝ)^(j+2) ≤ 2^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  simpa only [dgOscDyadicScale,show j+2 = (j+1)+1 by omega,pow_succ,mul_comm] using hh

theorem dgOscDyadicValue_later_neg {j k : ℕ} (hjk : j < k) {r : ℝ}
    (hj : dgOscDyadicValue j r < 1/2) : dgOscDyadicValue k r < 0 := by
  have haj := dgOscDyadicScale_pos j
  have hr : r-1 < 0 := by
    by_contra hn
    have hh := mul_nonneg haj.le (le_of_not_gt hn)
    dsimp only [dgOscDyadicValue] at hj
    nlinarith only [hj,hh]
  have hh := mul_le_mul_of_nonpos_right (dgOscDyadicScale_double_le hjk) hr.le
  dsimp only [dgOscDyadicValue] at hj ⊢
  nlinarith only [hj,hh]

theorem dgOscDyadicBand_pairwiseDisjoint {n : ℕ} (u : Point n → ℝ) :
    Pairwise (fun j k => Disjoint (dgOscDyadicBand u j) (dgOscDyadicBand u k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro p hpj hpk
  rcases lt_or_gt_of_ne hjk with h | h
  · have hh := dgOscDyadicValue_later_neg h hpj.2.2
    linarith only [hh,hpk.2.1]
  · have hh := dgOscDyadicValue_later_neg h hpk.2.2
    linarith only [hh,hpj.2.1]

theorem dgOsc_mid_finite (n : ℕ) : volume (dgMiddleCylinder n) < ⊤ := by
  have hh := dg_cylinder_measure_lt_top (0 : Space n) (7/4) (-3) 0
  rw [dg_productVolume_eq_restrict,Measure.restrict_apply_univ] at hh
  exact hh

theorem dgOscDyadicBand_sum_le {n N : ℕ} (u : Point n → ℝ)
    (hS : ∀ j < N, MeasurableSet (dgOscDyadicBand u j)) :
    (∑ j ∈ Finset.range N, volume.real (dgOscDyadicBand u j)) ≤ volume.real (dgMiddleCylinder n) := by
  have hd : PairwiseDisjoint (↑(Finset.range N)) (dgOscDyadicBand u) :=
    (dgOscDyadicBand_pairwiseDisjoint u).set_pairwise _
  have hfin (j : ℕ) : volume (dgOscDyadicBand u j) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (dgOsc_mid_finite n)).ne
  rw [←measureReal_biUnion_finset hd (fun j hj => hS j (Finset.mem_range.mp hj)) (fun j _ => hfin j)]
  apply measureReal_mono _ (dgOsc_mid_finite n).ne
  intro p hp
  obtain ⟨j,hj⟩ := mem_iUnion.mp hp
  obtain ⟨_,hpj⟩ := mem_iUnion.mp hj
  exact hpj.1

theorem dgOsc_pow_inverse (k : ℕ) : (2:ℝ)^k*(1/2:ℝ)^k = 1 := by
  rw [←mul_pow]
  norm_num

theorem dgOsc_forcing_budget {N j : ℕ} (hj : j < N) :
    2*dgOscDyadicScale j*(1/2:ℝ)^(N+3) ≤ 1 := by
  have hh : (2:ℝ)^(j+2) ≤ 2^(N+3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : 2*dgOscDyadicScale j = (2:ℝ)^(j+2) := by
    dsimp only [dgOscDyadicScale]
    rw [show j+2 = (j+1)+1 by omega,pow_succ]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hh (pow_nonneg (by norm_num) _)).trans_eq (dgOsc_pow_inverse _)

theorem dgOsc_epsilon_bounds (N : ℕ) : 0 < (1/2:ℝ)^(N+3) ∧ (1/2:ℝ)^(N+3) ≤ 1/4 := by
  refine ⟨pow_pos (by norm_num) _,?_⟩
  rw [show N+3 = (N+1)+2 by omega,pow_add]
  have hh := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := N+1)
  exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by norm_num)


theorem dgOsc_drop_budget {N j : ℕ} (hj : j < N) :
    4*dgOscDyadicScale j*(1/2:ℝ)^(N+3) ≤ 1 := by
  have hh : (2:ℝ)^(j+3) ≤ 2^(N+3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : 4*dgOscDyadicScale j = (2:ℝ)^(j+3) := by
    dsimp only [dgOscDyadicScale]
    rw [show j+3 = (j+1)+2 by omega,pow_add]
    norm_num
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hh (pow_nonneg (by norm_num) _)).trans_eq (dgOsc_pow_inverse _)

theorem dgOsc_ball_time_finite {n : ℕ} (x : Space n) (R a b : ℝ) :
    volume (Metric.ball x R ×ˢ Ioo a b) < ⊤ := by
  have hh := dg_cylinder_measure_lt_top x R a b
  rw [dg_productVolume_eq_restrict,Measure.restrict_apply_univ] at hh
  exact hh


/-- A fixed fraction of early low values yields an upper drop. Disjoint middle
bands force a small late high set, which is then the actual unit-cylinder
small-measure premise. No lower bound on this candidate is assumed. -/
theorem dgOsc_normalized_upper_drop {n : ℕ} (hn : 0 < n) {ν L : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ ε η : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η ≤ 1/4 ∧
      ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgSmCylinderOpen 2) A c f u → ClassicalDivEq (dgSmCylinderOpen 2) A c f u →
      DGUniformBounds (dgSmCylinderOpen 2) A c f ν L 1 ε →
      ContinuousOn u (dgSmCylinder 2) → (∀ p ∈ dgSmCylinder 2, u p ≤ 1) →
      (1/2)*volume.real (dgEarlyCylinder n) ≤ volume.real (dgEarlyCylinder n ∩ {p | u p ≤ 1/2}) →
      ∀ p ∈ dgSmCylinder (1/2), u p ≤ 1-η := by
  obtain ⟨δs,hδs,hδs1,hSmall⟩ := dg_small_measure n hn ν L hν hνL
  let β := δs/2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith only [hδs1]
  obtain ⟨δm,hδm,hMiddle⟩ := dg_intermediate_value hn hν hνL
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) ≤ 1) hβ hβ1
  let V := volume.real (dgMiddleCylinder n)
  obtain ⟨M,hM⟩ := exists_nat_gt (V/δm)
  let N := M+1
  have hN : V < (N:ℝ)*δm := by
    have hh := (div_lt_iff₀ hδm).mp hM
    dsimp only [N]
    norm_num only [Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,hδm]
  let ε : ℝ := (1/2)^(N+3)
  have hε := (dgOsc_epsilon_bounds N).1
  have hεq := (dgOsc_epsilon_bounds N).2
  refine ⟨ε,ε,hε,hεq.trans (by norm_num),hε,hεq,?_⟩
  intro A c f u hf hpde hb hu hupper hEarly
  let v : ℕ → Point n → ℝ := fun j p => dgOscDyadicValue j (u p)
  let fj : ℕ → Point n → ℝ := fun j p => dgOscDyadicScale j*f p
  have hFields (j : ℕ) : DGClassicalFields (dgSmCylinderOpen 2) A c (fj j) (v j) :=
    dgOsc_affine_fields hf (dgOscDyadicScale j) (dgOscDyadicScale j-1)
  have hPde (j : ℕ) : ClassicalDivEq (dgSmCylinderOpen 2) A c (fj j) (v j) :=
    dgClassicalDivEq_affine (dgSmCylinderOpen_isOpen 2) hf hpde (dgOscDyadicScale j) (dgOscDyadicScale j-1)
  have hRawBounds (j : ℕ) : DGUniformBounds (dgSmCylinderOpen 2) A c (fj j) ν L 1 (dgOscDyadicScale j*ε) := by
    simpa only [abs_of_pos (dgOscDyadicScale_pos j)] using dgOsc_affine_uniform (σ := dgOscDyadicScale j) hb
  have hForce (j : ℕ) (hj : j < N) : dgOscDyadicScale j*ε ≤ 1 := by
    have hh := dgOsc_forcing_budget hj
    have hp : 0 ≤ dgOscDyadicScale j*ε := mul_nonneg (dgOscDyadicScale_pos j).le hε.le
    change 2*dgOscDyadicScale j*ε ≤ 1 at hh
    nlinarith only [hh,hp]
  have hBounds (j : ℕ) (hj : j < N) : DGUniformBounds (dgSmCylinderOpen 2) A c (fj j) ν L 1 1 :=
    dgOsc_uniform_mono (hRawBounds j) (by norm_num) le_rfl (hForce j hj)
  have hCont (j : ℕ) : ContinuousOn (v j) (dgSmCylinder 2) :=
    (continuousOn_const.mul hu).sub continuousOn_const
  have hUpper (j : ℕ) (p : Point n) (hp : p ∈ dgSmCylinder 2) : v j p ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hupper p hp) (dgOscDyadicScale_pos j).le
    change dgOscDyadicScale j*u p-(dgOscDyadicScale j-1) ≤ 1
    nlinarith only [hh]
  have hMidSub : dgMiddleCylinder n ⊆ dgSmCylinderOpen 2 := by
    intro p hp
    refine ⟨Metric.ball_subset_ball (by norm_num : (7/4:ℝ) ≤ 2) hp.1,?_,hp.2.2⟩
    norm_num only [show -(2:ℝ)^2 = -4 by norm_num]
    linarith only [hp.2.1]
  have hBandMeas (j : ℕ) : MeasurableSet (dgOscDyadicBand u j) :=
    dg_local_band_measurable (Metric.isOpen_ball.prod isOpen_Ioo)
      ((hFields j).2.2.2.continuousOn.mono hMidSub) 0 (1/2)
  have hEarlyV (j : ℕ) : (1/2)*volume.real (dgEarlyCylinder n) ≤
      volume.real (dgEarlyCylinder n ∩ {p | v j p ≤ 0}) := by
    apply hEarly.trans
    apply measureReal_mono _ ((measure_mono inter_subset_left).trans_lt
      (dgOsc_ball_time_finite (0 : Space n) 1 (-3) (-2))).ne
    intro p hp
    refine ⟨hp.1,?_⟩
    have hh := mul_le_mul_of_nonneg_left hp.2 (dgOscDyadicScale_pos j).le
    have ha := dgOscDyadicScale_two_le j
    change dgOscDyadicScale j*u p-(dgOscDyadicScale j-1) ≤ 0
    nlinarith only [hh,ha]
  have hSlab : Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2:ℝ) 0 ⊆ dgSmCylinder 2 := by
    intro p hp
    refine ⟨hp.1,?_,hp.2.2⟩
    norm_num only [show -(2:ℝ)^2 = -4 by norm_num]
    linarith only [hp.2.1]
  have hRegion : Metric.ball (0 : Space n) 2 ×ˢ Ioc (-4:ℝ) 0 = dgSmCylinder 2 := by
    norm_num [dgSmCylinder]
  have hMiddleFields (j : ℕ) : DGClassicalFields (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c (fj j) (v j) := by
    simpa only [dgSmCylinderOpen,show -(2:ℝ)^2 = -4 by norm_num] using hFields j
  have hMiddlePde (j : ℕ) : ClassicalDivEq (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c (fj j) (v j) := by
    simpa only [dgSmCylinderOpen,show -(2:ℝ)^2 = -4 by norm_num] using hPde j
  have hMiddleBounds (j : ℕ) (hj : j < N) : DGUniformBounds (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c (fj j) ν L 1 1 := by
    simpa only [dgSmCylinderOpen,show -(2:ℝ)^2 = -4 by norm_num] using hBounds j hj
  have hSmallLate : ∃ j < N, volume.real (dgLateCylinder n ∩ {p | 1/2 ≤ v j p}) < β*volume.real (dgLateCylinder n) := by
    by_contra hAll
    push Not at hAll
    have hLower (j : ℕ) (hj : j < N) : δm ≤ volume.real (dgOscDyadicBand u j) :=
      hMiddle A c (fj j) (v j) (hMiddleFields j) (hMiddlePde j) (hMiddleBounds j hj)
        ((hCont j).mono hSlab) (fun p hp => hUpper j p (hRegion ▸ hp)) (hEarlyV j) (hAll j hj)
    have hSum : (N:ℝ)*δm ≤ ∑ j ∈ Finset.range N, volume.real (dgOscDyadicBand u j) := by
      have hh := Finset.sum_le_sum (fun j hj => hLower j (Finset.mem_range.mp hj))
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh
    exact (not_lt_of_ge (hSum.trans (dgOscDyadicBand_sum_le u (fun j _ => hBandMeas j)))) hN
  obtain ⟨j,hj,hLate⟩ := hSmallLate
  let w : Point n → ℝ := fun p => 2*v j p-1
  have hwFields := dgOsc_affine_fields (hFields j) 2 1
  have hwPde := dgClassicalDivEq_affine (dgSmCylinderOpen_isOpen 2) (hFields j) (hPde j) 2 1
  have hwForce : |(2:ℝ)| *(dgOscDyadicScale j*ε) ≤ 1 := by
    simpa only [abs_of_pos (by norm_num : (0:ℝ) < 2),mul_assoc] using dgOsc_forcing_budget hj
  have hwBounds := dgOsc_uniform_mono (dgOsc_affine_uniform (σ := 2) (hRawBounds j)) (by norm_num) le_rfl hwForce
  have hQ1 : dgSmCylinder (n := n) 1 ⊆ dgSmCylinder 2 := dgSmCylinder_subset (by norm_num) (by norm_num)
  have hQ1Open : dgSmCylinderOpen (n := n) 1 ⊆ dgSmCylinderOpen 2 := by
    intro p hp
    refine ⟨Metric.ball_subset_ball (by norm_num : (1:ℝ) ≤ 2) hp.1,?_,hp.2.2⟩
    norm_num only [show -(1:ℝ)^2 = -1 by norm_num,show -(2:ℝ)^2 = -4 by norm_num] at hp ⊢
    linarith only [hp.2.1]
  have hwCont : ContinuousOn w (dgSmCylinder 1) :=
    ((continuousOn_const.mul (hCont j)).sub continuousOn_const).mono hQ1
  have hwUpper (p : Point n) (hp : p ∈ dgSmCylinder 1) : w p ≤ 1 := by
    have hh := hUpper j p (hQ1 hp)
    dsimp only [w]
    linarith only [hh]
  have hLateEq : dgSmCylinderOpen (n := n) 1 = dgLateCylinder n := by norm_num [dgSmCylinderOpen,dgLateCylinder]
  have hLateFin : volume (dgLateCylinder n ∩ {p | 1/2 ≤ v j p}) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (dgOsc_ball_time_finite (0 : Space n) 1 (-1) 0)).ne
  have hSmallMeasure : dgSmSuperlevelMeasure 1 0 w ≤ δs*
      (productVolume (Metric.ball (0 : Space n) 1) (Ioo (-1) 0) univ).toReal := by
    rw [dgSmSuperlevelMeasure_eq_volume]
    have hSet : dgSmCylinderOpen 1 ∩ {p | 0 < w p} ⊆ dgLateCylinder n ∩ {p | 1/2 ≤ v j p} := by
      intro p hp
      refine ⟨hLateEq ▸ hp.1,?_⟩
      have hh : 0 < w p := hp.2
      dsimp only [w] at hh
      change (1/2:ℝ) ≤ v j p
      linarith only [hh]
    have hBudget : β*volume.real (dgLateCylinder n) ≤ δs*volume.real (dgLateCylinder n) :=
      mul_le_mul_of_nonneg_right (by dsimp only [β]; linarith only [hδs]) ENNReal.toReal_nonneg
    have hVolume : (productVolume (Metric.ball (0 : Space n) 1) (Ioo (-1) 0) univ).toReal = volume.real (dgLateCylinder n) := by
      rw [dg_productVolume_eq_restrict,Measure.restrict_apply_univ]
      rfl
    rw [hVolume]
    exact (measureReal_mono hSet hLateFin).trans (hLate.le.trans hBudget)
  have hDrop := hSmall A c (fun p => 2*fj j p) w
    (dgOsc_fields_mono hQ1Open hwFields) (fun p hp => hwPde p (hQ1Open hp))
    (dgOsc_uniform_restrict hQ1Open hwBounds) hwCont hwUpper hSmallMeasure
  intro p hp
  have hh := hDrop p hp
  have hBudget := dgOsc_drop_budget hj
  change 4*dgOscDyadicScale j*ε ≤ 1 at hBudget
  apply (mul_le_mul_iff_right₀ (dgOscDyadicScale_pos j)).mp
  dsimp only [w,v,dgOscDyadicValue] at hh
  nlinarith only [hh,hBudget]


/-- The normalized oscillation alternative follows by applying the actual
upper-drop theorem to u or 1-u. Nonnegative normalization is an explicit premise
here and will be supplied from a containing value interval below. -/
theorem dgOsc_normalized_alternative {n : ℕ} (hn : 0 < n) {ν L : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ ε η : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η ≤ 1/4 ∧
      ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgSmCylinderOpen 2) A c f u → ClassicalDivEq (dgSmCylinderOpen 2) A c f u →
      DGUniformBounds (dgSmCylinderOpen 2) A c f ν L 1 ε →
      ContinuousOn u (dgSmCylinder 2) → (∀ p ∈ dgSmCylinder 2, 0 ≤ u p ∧ u p ≤ 1) →
      (∀ p ∈ dgSmCylinder (1/2), u p ≤ 1-η) ∨ (∀ p ∈ dgSmCylinder (1/2), η ≤ u p) := by
  obtain ⟨ε,η,hε,hε1,hη,hηq,hDrop⟩ := dgOsc_normalized_upper_drop hn hν hνL
  refine ⟨ε,η,hε,hε1,hη,hηq,?_⟩
  intro A c f u hf hpde hb hu hRange
  let E := dgEarlyCylinder n
  let Low := E ∩ {p | u p ≤ 1/2}
  let High := E ∩ {p | 1/2 ≤ u p}
  have hPart : E = Low ∪ High := by
    ext p
    constructor
    · intro hp
      rcases le_total (u p) (1/2) with hh | hh
      · exact Or.inl ⟨hp,hh⟩
      · exact Or.inr ⟨hp,hh⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hMass : volume.real E ≤ volume.real Low+volume.real High := by
    rw [hPart]
    exact measureReal_union_le _ _
  by_cases hLow : (1/2)*volume.real E ≤ volume.real Low
  · exact Or.inl (hDrop A c f u hf hpde hb hu (fun p hp => (hRange p hp).2) hLow)
  · have hHigh : (1/2)*volume.real E ≤ volume.real High := by
      linarith only [hMass,lt_of_not_ge hLow]
    let w : Point n → ℝ := fun p => (-1)*u p-(-1)
    have hwFields := dgOsc_affine_fields hf (-1) (-1)
    have hwPde := dgClassicalDivEq_affine (dgSmCylinderOpen_isOpen 2) hf hpde (-1) (-1)
    have hwBounds := dgOsc_affine_uniform (σ := (-1:ℝ)) hb
    norm_num only [abs_neg,abs_one,one_mul] at hwBounds
    have hwCont : ContinuousOn w (dgSmCylinder 2) := (continuousOn_const.mul hu).sub continuousOn_const
    have hwUpper (p : Point n) (hp : p ∈ dgSmCylinder 2) : w p ≤ 1 := by
      have hh := (hRange p hp).1
      dsimp only [w]
      linarith only [hh]
    have hSet : High = E ∩ {p | w p ≤ 1/2} := by
      ext p
      change (p ∈ E ∧ (1/2:ℝ) ≤ u p) ↔ (p ∈ E ∧ (-1)*u p-(-1) ≤ 1/2)
      constructor
      · intro hp; exact ⟨hp.1,by linarith only [hp.2]⟩
      · intro hp; exact ⟨hp.1,by linarith only [hp.2]⟩
    rw [hSet] at hHigh
    have hwDrop := hDrop A c (fun p => (-1)*f p) w hwFields hwPde hwBounds hwCont hwUpper hHigh
    refine Or.inr (fun p hp => ?_)
    have hh := hwDrop p hp
    dsimp only [w] at hh
    linarith only [hh]


/-- Every genuine containing value interval shrinks on the quarter cylinder,
with the actual squared-radius forcing error. The constants precede D,F, the
center/radius and every coefficient/solution; no gradient norm is quantitative. -/
theorem dgOsc_interval_shrink {n : ℕ} (hn : 0 < n) {ν L : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ θ K : ℝ, 0 < θ ∧ θ < 1 ∧ 3/4 ≤ θ ∧ 0 < K ∧
      ∀ D F : ℝ, 0 ≤ D → 0 ≤ F → ∀ (p₀ : Point n) (R : ℝ), 0 < R → R ≤ dgOscDriftRadius D →
      ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgOscCylinderOpen p₀ R) A c f u → ClassicalDivEq (dgOscCylinderOpen p₀ R) A c f u →
      DGUniformBounds (dgOscCylinderOpen p₀ R) A c f ν L D F → ContinuousOn u (dgOscCylinder p₀ R) →
      ∀ ell width : ℝ, 0 ≤ width → (∀ p ∈ dgOscCylinder p₀ R, ell ≤ u p ∧ u p ≤ ell+width) →
      ∃ ell' : ℝ, ∀ p ∈ dgOscCylinder p₀ (R/4), ell' ≤ u p ∧ u p ≤ ell'+(θ*width+K*F*R^2) := by
  obtain ⟨ε,η,hε,hε1,hη,hηq,hAlternative⟩ := dgOsc_normalized_alternative hn hν hνL
  let θ := 1-η
  let K := 1/ε
  have hθ : 0 < θ := by dsimp only [θ]; linarith only [hηq]
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith only [hη]
  have hθq : 3/4 ≤ θ := by dsimp only [θ]; linarith only [hηq]
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨θ,K,hθ,hθ1,hθq,hK,?_⟩
  intro D F hD hF p₀ R hR hRs A c f u hf hpde hb hu ell width hwidth hRange
  have hInnerOuter : dgOscCylinder p₀ (R/4) ⊆ dgOscCylinder p₀ R :=
    dgOscCylinder_subset (by positivity) (by linarith only [hR])
  have hError : 0 ≤ K*F*R^2 := by positivity
  by_cases hwidth0 : width = 0
  · refine ⟨ell,fun p hp => ?_⟩
    have hh := hRange p (hInnerOuter hp)
    rw [hwidth0,add_zero] at hh
    exact ⟨hh.1,hh.2.trans (by rw [hwidth0,mul_zero,zero_add]; linarith only [hError])⟩
  have hwidthpos : 0 < width := lt_of_le_of_ne hwidth (Ne.symm hwidth0)
  let ρ := R/2
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρR : ρ*2 = R := by dsimp only [ρ]; ring
  have hρr : ρ*(1/2) = R/4 := by dsimp only [ρ]; ring
  have hMapOpen : MapsTo (dgOscMap p₀ ρ) (dgSmCylinderOpen 2) (dgOscCylinderOpen p₀ R) := by
    intro p hp
    simpa only [hρR] using (dgOscMap_mem_open_cylinder_iff p₀ hρ 2 p).mpr hp
  have hMapClosed : MapsTo (dgOscMap p₀ ρ) (dgSmCylinder 2) (dgOscCylinder p₀ R) := by
    intro p hp
    simpa only [hρR] using (dgOscMap_mem_cylinder_iff p₀ hρ 2 p).mpr hp
  have hMapInner (p : Point n) (hp : p ∈ dgOscCylinder p₀ (R/4)) :
      dgOscUnmap p₀ ρ p ∈ dgSmCylinder (1/2) := by
    apply (dgOscMap_mem_cylinder_iff p₀ hρ (1/2) _).mp
    rw [dgOscMap_unmap p₀ hρ.ne',hρr]
    exact hp
  by_cases hSmallForce : (ρ^2*F)/width ≤ ε
  · let As := fun p => A (dgOscMap p₀ ρ p)
    let cs := fun p i => ρ*c (dgOscMap p₀ ρ p) i
    let fs := fun p => ρ^2*f (dgOscMap p₀ ρ p)
    let us := fun p => u (dgOscMap p₀ ρ p)
    let v := fun p => width⁻¹*us p-ell/width
    let fv := fun p => width⁻¹*fs p
    have hScaledFields : DGClassicalFields (dgSmCylinderOpen 2) As cs fs us := dgOsc_scaled_fields p₀ ρ hMapOpen hf
    have hScaledPde : ClassicalDivEq (dgSmCylinderOpen 2) As cs fs us :=
      dgOsc_scaled_equation (Metric.isOpen_ball.prod isOpen_Ioo) (dgSmCylinderOpen_isOpen 2) p₀ ρ hMapOpen hf hpde
    have hScaledBounds : DGUniformBounds (dgSmCylinderOpen 2) As cs fs ν L (|ρ| *D) (ρ^2*F) :=
      dgOsc_scaled_uniform p₀ ρ hMapOpen hb
    have hVFields : DGClassicalFields (dgSmCylinderOpen 2) As cs fv v := dgOsc_affine_fields hScaledFields (width⁻¹) (ell/width)
    have hVPde : ClassicalDivEq (dgSmCylinderOpen 2) As cs fv v :=
      dgClassicalDivEq_affine (dgSmCylinderOpen_isOpen 2) hScaledFields hScaledPde (width⁻¹) (ell/width)
    have hVForce : |width⁻¹| *(ρ^2*F) ≤ ε := by
      rw [abs_of_pos (inv_pos.mpr hwidthpos)]
      simpa only [div_eq_mul_inv,mul_comm] using hSmallForce
    have hVBounds : DGUniformBounds (dgSmCylinderOpen 2) As cs fv ν L 1 ε :=
      dgOsc_uniform_mono (dgOsc_affine_uniform (σ := width⁻¹) hScaledBounds)
        (mul_nonneg (abs_nonneg _) hD) (dgOsc_scaled_drift_le_one hD hR hRs) hVForce
    have hUSCont : ContinuousOn us (dgSmCylinder 2) := hu.comp (dgOscMap_contDiff p₀ ρ).continuous.continuousOn hMapClosed
    have hVCont : ContinuousOn v (dgSmCylinder 2) := (continuousOn_const.mul hUSCont).sub continuousOn_const
    have hVal (p : Point n) : v p = (us p-ell)/width := by dsimp only [v]; ring
    have hVRange (p : Point n) (hp : p ∈ dgSmCylinder 2) : 0 ≤ v p ∧ v p ≤ 1 := by
      have hh := hRange (dgOscMap p₀ ρ p) (hMapClosed hp)
      rw [hVal]
      exact ⟨div_nonneg (sub_nonneg.mpr hh.1) hwidthpos.le,(div_le_one hwidthpos).mpr (by linarith only [hh.2])⟩
    have hValInv (p : Point n) : v (dgOscUnmap p₀ ρ p) = (u p-ell)/width := by
      rw [hVal]
      dsimp only [us]
      rw [dgOscMap_unmap p₀ hρ.ne']
    rcases hAlternative As cs fv v hVFields hVPde hVBounds hVCont hVRange with hUpper | hLower
    · refine ⟨ell,fun p hp => ?_⟩
      have hOrig := hRange p (hInnerOuter hp)
      have hh := hUpper _ (hMapInner p hp)
      rw [hValInv] at hh
      have hh' := (div_le_iff₀ hwidthpos).mp hh
      exact ⟨hOrig.1,by dsimp only [θ]; nlinarith only [hh',hError]⟩
    · refine ⟨ell+η*width,fun p hp => ?_⟩
      have hOrig := hRange p (hInnerOuter hp)
      have hh := hLower _ (hMapInner p hp)
      rw [hValInv] at hh
      have hh' := (le_div_iff₀ hwidthpos).mp hh
      exact ⟨by linarith only [hh'],by dsimp only [θ]; nlinarith only [hOrig.2,hError]⟩
  · have hLarge : ε*width < ρ^2*F := (lt_div_iff₀ hwidthpos).mp (lt_of_not_ge hSmallForce)
    have hρF : ρ^2*F ≤ R^2*F := by
      apply mul_le_mul_of_nonneg_right _ hF
      dsimp only [ρ]
      nlinarith only [sq_nonneg R]
    have hWidth : width ≤ K*F*R^2 := calc
      _ ≤ (F*R^2)/ε := (le_div_iff₀ hε).mpr (by nlinarith only [hLarge,hρF])
      _ = _ := by dsimp only [K]; ring
    refine ⟨ell,fun p hp => ?_⟩
    have hh := hRange p (hInnerOuter hp)
    have hp0 := mul_nonneg hθ.le hwidth
    exact ⟨hh.1,hh.2.trans (by linarith only [hWidth,hp0])⟩

end Yau.LeafProofs.L16Aux
