import Yau.Proofs.F03DirichletHeatDerivative

/-! The supported energy and heat paths in the original ambient completion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- Actual zero extension preserves the real L² pairing. -/
theorem l2ZeroExtension_inner {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (O : Set α) (hO : MeasurableSet O)
    (f k : Lp ℝ 2 (μ.restrict O)) :
    ⟪l2ZeroExtension μ O hO f, l2ZeroExtension μ O hO k⟫_ℝ = ⟪f,k⟫_ℝ := by
  have h := @norm_add_sq ℝ _ _ _ _ (l2ZeroExtension μ O hO f) (l2ZeroExtension μ O hO k)
  rw [← map_add, l2ZeroExtension_norm, l2ZeroExtension_norm, l2ZeroExtension_norm] at h
  have h' := @norm_add_sq ℝ _ _ _ _ f k
  simp only [RCLike.re_to_real] at h h'
  linarith

/-- The closed energy is exactly the ambient closed energy on the actual
subspace; zero extension changes neither scalar pairing nor normalization. -/
theorem dirichletClosedEnergy_eq_ambient (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u v : DirichletEnergy g μ hμ O) :
    dirichletClosedEnergy g μ hμ O u v = scalarClosedEnergy g μ hμ u.val v.val := by
  unfold dirichletClosedEnergy scalarClosedEnergy
  change ⟪u.val,v.val⟫_ℝ - _ = _
  rw [← dirichletL2_zeroExtension g μ hμ O hO u,
    ← dirichletL2_zeroExtension g μ hμ O hO v, l2ZeroExtension_inner]

/-- The original energy completion, with its original metric and volume. -/
def dirichletAmbientHeatEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (t : ℝ) :
    Lp ℝ 2 (μ.restrict O) →L[ℝ] ScalarEnergySpace g μ hμ :=
  (dirichletEnergySubmodule g μ hμ O).subtypeL.comp (dirichletHeatEnergy g μ hμ O t)

theorem dirichletAmbientHeatEnergy_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    scalarEnergyL2 g μ hμ (dirichletAmbientHeatEnergy g μ hμ O t f) =
      l2ZeroExtension μ O hO (dirichletHeat g μ hμ O t f) := by
  rw [← dirichletHeatEnergy_L2 g μ hμ O ht f]
  exact (dirichletL2_zeroExtension g μ hμ O hO _).symm

theorem dirichletAmbientHeatEnergy_continuousAt (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict O)) :
    ContinuousAt (fun s => dirichletAmbientHeatEnergy g μ hμ O s f) t :=
  (dirichletEnergySubmodule g μ hμ O).subtypeL.continuous.continuousAt.comp
    (dirichletHeatEnergy_continuousAt g μ hμ O ht f)

/-- The constructed supported heat lift is a genuine Bochner L² energy
path on each positive finite time slab. -/
theorem dirichletHeatEnergy_memLp_slab (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) {l r : ℝ} (hl : 0 < l) :
    MemLp (fun t => dirichletHeatEnergy g μ hμ O t f) 2
      (volume.restrict (Set.Ioo l r)) := by
  let W := fun t => dirichletHeatEnergy g μ hμ O t f
  have hc : ContinuousOn W (Set.Icc l r) := fun t ht =>
    (dirichletHeatEnergy_continuousAt g μ hμ O (hl.trans_le ht.1) f).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  apply MemLp.of_bound ((hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC ⟨t,Set.Ioo_subset_Icc_self ht,rfl⟩

theorem dirichletAmbientHeatEnergy_memLp_slab (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) {l r : ℝ} (hl : 0 < l) :
    MemLp (fun t => dirichletAmbientHeatEnergy g μ hμ O t f) 2
      (volume.restrict (Set.Ioo l r)) :=
  (dirichletEnergySubmodule g μ hμ O).subtypeL.comp_memLp'
    (dirichletHeatEnergy_memLp_slab g μ hμ O f hl)

end Yau.Proofs.F03Aux
