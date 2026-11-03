import Yau.Proofs.P02BisectionalContinuity

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem coordinateRm_smul_four (h : HermitianField M) (c : M.Carrier)
    (z U V W T : ComplexVector n) (a b d e : ℝ) :
    coordinateRm h c z (a • U) (b • V) (d • W) (e • T) =
      (a*b*d*e) * coordinateRm h c z U V W T := by
  have hr (r : ℝ) (v : ComplexVector n) (i : RIdx n) :
      realCoord (r • v) i = r * realCoord v i := by
    rw [← realCoordCLM_apply, map_smul, realCoordCLM_apply, smul_eq_mul]
  unfold coordinateRm
  simp only [hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem coordinateBisectional_smul (h : HermitianField M) (c : M.Carrier)
    (z U V : ComplexVector n) (a b : ℝ) :
    coordinateBisectional h c z (a • U) (b • V) =
      (a^2*b^2) * coordinateBisectional h c z U V := by
  have hI : Complex.I • (b • V) = b • (Complex.I • V) := (smul_comm b Complex.I V).symm
  unfold coordinateBisectional
  rw [hI, coordinateRm_smul_four, coordinateRm_smul_four]
  ring

theorem coordinateBisectional_zero_left (h : HermitianField M) (c : M.Carrier)
    (z V : ComplexVector n) : coordinateBisectional h c z 0 V = 0 := by
  simp [coordinateBisectional, coordinateRm, realCoord]

theorem coordinateBisectional_zero_right (h : HermitianField M) (c : M.Carrier)
    (z U : ComplexVector n) : coordinateBisectional h c z U 0 = 0 := by
  simp [coordinateBisectional, coordinateRm, realCoord]

theorem transportBisectional_smul (h : HermitianField M)
    (y : M.Carrier) (U V : TangentSpace 𝓘(ℝ, ComplexVector n) y) (a b : ℝ) :
    transportBisectional h ⟨y, (a • U,b • V)⟩ =
      (a^2*b^2)*transportBisectional h ⟨y, (U,V)⟩ := by
  have H (Z : TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    realTangentCoords_eq_complex_coords y y (mem_chart_source _ _) Z
  rw [transportBisectional, transportBisectional, paperBisectional_eq_coordinate,
    paperBisectional_eq_coordinate, ← H (a • U), ← H (b • V), ← H U, ← H V,
    map_smul, map_smul]
  exact coordinateBisectional_smul h y (chartPt y y) _ _ a b

theorem transportBisectional_pos (h : HermitianField M) (hp : PaperPositiveBisectional h)
    (y : M.Carrier) (U V : TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hU : U ≠ 0) (hV : V ≠ 0) : 0 < transportBisectional h ⟨y,(U,V)⟩ := by
  apply hp y
  · intro he
    apply hU
    exact (realTangentEquiv y).injective (he.trans (map_zero _).symm)
  · intro he
    apply hV
    exact (realTangentEquiv y).injective (he.trans (map_zero _).symm)

theorem transportBisectional_nonneg (h : HermitianField M) (hp : PaperPositiveBisectional h)
    (y : M.Carrier) (U V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    0 ≤ transportBisectional h ⟨y,(U,V)⟩ := by
  by_cases hU : U = 0
  · subst U
    rw [transportBisectional, paperBisectional_eq_coordinate,
      ← realTangentCoords_eq_complex_coords y y (mem_chart_source _ _) 0,
      ← realTangentCoords_eq_complex_coords y y (mem_chart_source _ _) V, map_zero,
      coordinateBisectional_zero_left]
  by_cases hV : V = 0
  · subst V
    rw [transportBisectional, paperBisectional_eq_coordinate,
      ← realTangentCoords_eq_complex_coords y y (mem_chart_source _ _) U,
      ← realTangentCoords_eq_complex_coords y y (mem_chart_source _ _) 0, map_zero,
      coordinateBisectional_zero_right]
  exact (transportBisectional_pos h hp y U V hU hV).le

theorem compact_bisectional_lower_bound (g : SmoothMetric M)
    (hp : PaperPositiveBisectional g.form) (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y ∈ K,
      ∀ U V : TangentSpace 𝓘(ℝ, ComplexVector n) y,
      κ * (underlyingRealRiemannianMetric g.form).inner y U U *
          (underlyingRealRiemannianMetric g.form).inner y V V ≤
        transportBisectional g.form ⟨y,(U,V)⟩ := by
  letI := manifold_realSmooth M
  let S : Set (realTransportBundle M) := {q | q.proj ∈ K ∧
    realTangentEnergy g.form (realTransportDiag q).1 = 1 ∧
    realTangentEnergy g.form (realTransportDiag q).2 = 1}
  have hd : Continuous (realTransportDiag (M := M)) :=
    (FiberBundle.Prod.isInducing_diag
      (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))
      (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))).continuous
  have hE1 : Continuous (fun q : realTransportBundle M =>
      realTangentEnergy g.form (realTransportDiag q).1) :=
    (realTangentEnergy_contMDiff g).continuous.comp hd.fst
  have hE2 : Continuous (fun q : realTransportBundle M =>
      realTangentEnergy g.form (realTransportDiag q).2) :=
    (realTangentEnergy_contMDiff g).continuous.comp hd.snd
  have hSc : IsCompact S := by
    have hclosed1 : IsClosed {q : realTransportBundle M |
        realTangentEnergy g.form (realTransportDiag q).1 = 1} :=
      isClosed_eq hE1 continuous_const
    have hclosed2 : IsClosed {q : realTransportBundle M |
        realTangentEnergy g.form (realTransportDiag q).2 = 1} :=
      isClosed_eq hE2 continuous_const
    have HS := (isCompact_realTransportEnergy_sublevel g hK 1 1).inter_right
      (hclosed1.inter hclosed2)
    convert HS using 1
    ext q
    simp only [S, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro hq
      exact ⟨⟨hq.1,hq.2.1.le,hq.2.2.le⟩,hq.2⟩
    · intro hq
      exact ⟨hq.1.1,hq.2⟩
  have hpos (q : realTransportBundle M) (hq : q ∈ S) : 0 < transportBisectional g.form q := by
    apply transportBisectional_pos g.form hp q.proj q.2.1 q.2.2
    · intro hzero
      have H := hq.2.1
      change (underlyingRealRiemannianMetric g.form).inner q.proj q.2.1 q.2.1 = 1 at H
      simp only [hzero,map_zero,ContinuousLinearMap.zero_apply] at H
      norm_num at H
    · intro hzero
      have H := hq.2.2
      change (underlyingRealRiemannianMetric g.form).inner q.proj q.2.2 q.2.2 = 1 at H
      simp only [hzero,map_zero,ContinuousLinearMap.zero_apply] at H
      norm_num at H
  obtain ⟨κ,hκ,hmin⟩ := hSc.exists_forall_le'
    (transportBisectional_continuous g.form (metricSmooth_of_smoothMetric g)).continuousOn hpos
  refine ⟨κ,hκ,?_⟩
  intro y hy U V
  by_cases hU : U = 0
  · subst U
    simpa only [map_zero, ContinuousLinearMap.zero_apply, mul_zero, zero_mul] using
      transportBisectional_nonneg g.form hp y 0 V
  by_cases hV : V = 0
  · subst V
    simpa only [map_zero, ContinuousLinearMap.zero_apply, mul_zero] using
      transportBisectional_nonneg g.form hp y U 0
  let EU := (underlyingRealRiemannianMetric g.form).inner y U U
  let EV := (underlyingRealRiemannianMetric g.form).inner y V V
  have hEU : 0 < EU := (underlyingRealRiemannianMetric g.form).pos y U hU
  have hEV : 0 < EV := (underlyingRealRiemannianMetric g.form).pos y V hV
  let r := Real.sqrt EU
  let s := Real.sqrt EV
  have hr : 0 < r := Real.sqrt_pos.mpr hEU
  have hs : 0 < s := Real.sqrt_pos.mpr hEV
  have hr2 : r^2 = EU := Real.sq_sqrt hEU.le
  have hs2 : s^2 = EV := Real.sq_sqrt hEV.le
  let U' := r⁻¹ • U
  let V' := s⁻¹ • V
  have hU' : (underlyingRealRiemannianMetric g.form).inner y U' U' = 1 := by
    change (underlyingRealRiemannianMetric g.form).inner y (r⁻¹ • U) (r⁻¹ • U) = 1
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change r⁻¹ * (r⁻¹ * EU) = 1
    rw [← hr2]
    field_simp
    <;> ring
  have hV' : (underlyingRealRiemannianMetric g.form).inner y V' V' = 1 := by
    change (underlyingRealRiemannianMetric g.form).inner y (s⁻¹ • V) (s⁻¹ • V) = 1
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change s⁻¹ * (s⁻¹ * EV) = 1
    rw [← hs2]
    field_simp
    <;> ring
  have hnorm : (⟨y,(U',V')⟩ : realTransportBundle M) ∈ S := ⟨hy,hU',hV'⟩
  have Hmin := hmin _ hnorm
  have hUeq : r • U' = U := by simp [U', smul_smul, hr.ne']
  have hVeq : s • V' = V := by simp [V', smul_smul, hs.ne']
  have Hscale := transportBisectional_smul g.form y U' V' r s
  rw [hUeq,hVeq,hr2,hs2] at Hscale
  rw [Hscale]
  change κ * EU * EV ≤ EU * EV * transportBisectional g.form ⟨y,(U',V')⟩
  nlinarith [mul_le_mul_of_nonneg_left Hmin (mul_pos hEU hEV).le]

end Yau.NodeProofs.P02Aux
