import Yau.Proofs.V02FlowPicardOperator

/-! The same-radius invariant ball and contraction for the genuine Picard operator. -/

open scoped Topology ContDiff NNReal
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V]

theorem picardExtension_image {a : V} {d R : ℝ}
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R)
    {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    compactExtension u p ∈ closedBall a (2 * d) := by
  rw [compactExtension_of_mem u hp]
  exact picardHolomorphicBall_image a hu _

theorem picardIntegrand_continuousOn {a : V} {d R : ℝ} {Ω : Set V} {W : V → V}
    (hW : ContinuousOn W Ω) (hball : closedBall a (2 * d) ⊆ Ω)
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R)
    {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    ContinuousOn (fun s : ℝ => W (compactExtension u (picardRadialLinear s p)))
      (Set.uIcc 0 1) := by
  have hr : Continuous (fun s : ℝ => picardRadialLinear s p) :=
    (continuous_picardRadialLinear (V := V)).clm_apply continuous_const
  have hmap : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      picardRadialLinear s p ∈ picardClosedDomain a d R :=
    fun s hs => picardRadialLinear_mem_closed (by simpa using hs) hp
  exact hW.comp ((continuousOn_compactExtension u).comp hr.continuousOn hmap)
    (fun s hs => hball (picardExtension_image hu (hmap s hs)))

theorem norm_picardIntegral_le {a : V} {d R M : ℝ} {W : V → V}
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R)
    {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    ‖picardIntegral W u p‖ ≤ M := by
  simpa only [picardIntegral, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := M) (f := fun s => W (compactExtension u (picardRadialLinear s p)))
      (fun s hs => hbound _ (picardExtension_image hu
        (picardRadialLinear_mem_closed (by simpa using Set.uIoc_subset_uIcc hs) hp)))

theorem picardRaw_displacement {a : V} {d R M : ℝ} {W : V → V}
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R)
    {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    ‖picardRaw W u p - p.2‖ ≤ ‖p.1‖ * M := by
  simpa only [picardRaw, add_sub_cancel_left, norm_smul] using
    mul_le_mul_of_nonneg_left (norm_picardIntegral_le hbound hu hp) (norm_nonneg p.1)

theorem norm_picardIntegral_sub_le {a : V} {d R : ℝ} {L : ℝ≥0}
    {Ω : Set V} {W : V → V} (hW : ContinuousOn W Ω)
    (hball : closedBall a (2 * d) ⊆ Ω)
    (hLip : LipschitzOnWith L W (closedBall a (2 * d)))
    {u v : C(picardClosedDomain a d R, V)}
    (hu : u ∈ picardHolomorphicBall a d R) (hv : v ∈ picardHolomorphicBall a d R)
    {p : ℂ × V} (hp : p ∈ picardClosedDomain a d R) :
    ‖picardIntegral W u p - picardIntegral W v p‖ ≤ L * dist u v := by
  have hui : IntervalIntegrable (fun s => W (compactExtension u (picardRadialLinear s p)))
      volume 0 1 := (picardIntegrand_continuousOn hW hball hu hp).intervalIntegrable
  have hvi : IntervalIntegrable (fun s => W (compactExtension v (picardRadialLinear s p)))
      volume 0 1 := (picardIntegrand_continuousOn hW hball hv hp).intervalIntegrable
  rw [picardIntegral, picardIntegral, ← intervalIntegral.integral_sub hui hvi]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := L * dist u v) ?_).trans_eq
    (by simp)
  intro s hs
  have hm := picardRadialLinear_mem_closed (by simpa using Set.uIoc_subset_uIcc hs) hp
  have hb := hLip.dist_le_mul _ (picardExtension_image hu hm) _ (picardExtension_image hv hm)
  rw [dist_eq_norm] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  rw [compactExtension_of_mem u hm, compactExtension_of_mem v hm]
  simpa only [dist_eq_norm, ContinuousMap.sub_apply] using
    (u - v).norm_coe_le_norm ⟨picardRadialLinear s p, hm⟩

def picardMap {a : V} {d R M : ℝ} {Ω : Set V} {W : V → V}
    (hW : ContinuousOn W Ω) (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    (u : picardHolomorphicBall a d R) : C(picardClosedDomain a d R, V) :=
  ⟨fun p => picardRaw W u.1 p.1,
    continuousOn_iff_continuous_domRestrict.mp
      (picardRaw_continuousOn_closed hW hball hbound u.2)⟩

theorem picardMap_mem {a : V} {d R M : ℝ} {Ω : Set V} {W : V → V}
    (hΩ : IsOpen Ω) (hW : DifferentiableOn ℂ W Ω)
    (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    (hM : 0 ≤ M) (hRM : R * M ≤ d)
    (u : picardHolomorphicBall a d R) :
    picardMap hW.continuousOn hball hbound u ∈ picardHolomorphicBall a d R := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have heq : compactExtension (picardMap hW.continuousOn hball hbound u) =ᶠ[𝓝 p]
        picardRaw W u.1 := by
      filter_upwards [(picardOpenDomain_isOpen a d R).mem_nhds hp] with q hq
      rw [compactExtension_of_mem _ (picardOpenDomain_subset_closedDomain a d R hq)]
      rfl
    exact (((picardRaw_differentiableOn_open hΩ hW hball u.2) p hp).differentiableAt
      ((picardOpenDomain_isOpen a d R).mem_nhds hp)).congr_of_eventuallyEq heq
      |>.differentiableWithinAt
  · rw [mem_closedBall, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (by
      have hnonempty := u.2.2
      exact le_trans (dist_nonneg : 0 ≤ dist u.1 (picardProjection a d R)) hnonempty)).mpr
    intro p
    change ‖picardRaw W u.1 p.1 - p.1.2‖ ≤ d
    exact (picardRaw_displacement hbound u.2 p.2).trans
      ((mul_le_mul_of_nonneg_right (by simpa using p.2.1) hM).trans hRM)

theorem picardMap_dist_le {a : V} {d R M : ℝ} {L : ℝ≥0}
    {Ω : Set V} {W : V → V} (hW : ContinuousOn W Ω)
    (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    (hLip : LipschitzOnWith L W (closedBall a (2 * d)))
    (u v : picardHolomorphicBall a d R) (hR : 0 ≤ R) :
    dist (picardMap hW hball hbound u) (picardMap hW hball hbound v) ≤
      (R * L) * dist u v := by
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  change ‖picardRaw W u.1 p.1 - picardRaw W v.1 p.1‖ ≤ _
  rw [picardRaw, picardRaw, add_sub_add_left_eq_sub, ← smul_sub, norm_smul]
  exact (mul_le_mul_of_nonneg_left (norm_picardIntegral_sub_le hW hball hLip u.2 v.2 p.2)
    (norm_nonneg p.1.1)).trans (by
      have ht : ‖p.1.1‖ ≤ R := by simpa using p.2.1
      have hd : 0 ≤ dist u.1 v.1 := dist_nonneg
      change ‖p.1.1‖ * (L * dist u.1 v.1) ≤ R * L * dist u.1 v.1
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right ht (mul_nonneg L.coe_nonneg hd))

theorem exists_picard_fixedPoint {a : V} {d R M : ℝ} {L : ℝ≥0}
    {Ω : Set V} {W : V → V} (hΩ : IsOpen Ω) (hW : DifferentiableOn ℂ W Ω)
    (hd : 0 ≤ d) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    (hLip : LipschitzOnWith L W (closedBall a (2 * d)))
    (hRM : R * M ≤ d) (hRL : R * L ≤ 1 / 2) :
    ∃ u : C(picardClosedDomain a d R, V), u ∈ picardHolomorphicBall a d R ∧
      ∀ p : picardClosedDomain a d R, u p = picardRaw W u p.1 := by
  let Γ := picardHolomorphicBall a d R
  letI : Nonempty Γ := ⟨⟨picardProjection a d R, picardProjection_mem_holomorphicBall a hd⟩⟩
  letI : CompleteSpace Γ := (picardHolomorphicBall_isClosed a d R).isComplete.completeSpace_coe
  let P : Γ → Γ := fun u => ⟨picardMap hW.continuousOn hball hbound u,
    picardMap_mem hΩ hW hball hbound hM hRM u⟩
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) P := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    exact (picardMap_dist_le hW.continuousOn hball hbound hLip u v hR).trans
      (mul_le_mul_of_nonneg_right hRL dist_nonneg)
  let u := ContractingWith.fixedPoint P hcontr
  refine ⟨u.1, u.2, fun p => ?_⟩
  have hfix : P u = u := hcontr.fixedPoint_isFixedPt
  exact (congrArg (fun v : Γ => v.1 p) hfix).symm

end Yau.Blueprint.V02FlowProof
