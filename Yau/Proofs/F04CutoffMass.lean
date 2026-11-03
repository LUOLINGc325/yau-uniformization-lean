import Yau.Proofs.F04C1CompactMass

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem smoothSpaceC1Time_mul {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    {v w : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I) (hw : SmoothSpaceC1Time w I) :
    SmoothSpaceC1Time (fun x t => v x t * w x t) I :=
  ⟨fun t ht => LeafProofs.L18Aux.smoothFn_mul (hv.1 t ht) (hw.1 t ht),
    fun x => (hv.2 x).mul (hw.2 x)⟩

theorem smoothSpaceC1Time_spatial_const {n : ℕ} {M : ComplexManifold n}
    {I : Set ℝ} {φ : M.Carrier → ℝ} (hφ : SmoothFn φ) :
    SmoothSpaceC1Time (fun x _t => φ x) I := by
  refine ⟨fun _ _ => hφ, fun x => ?_⟩
  exact ((hφ x).of_le (by norm_num)).comp contDiffOn_fst (fun _ hp => hp.1)

theorem cutoff_mass_differentiation {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {S : ℝ} {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v (Icc 0 S))
    {φ : M.Carrier → ℝ} (hφ : SmoothFn φ) (hcφ : HasCompactSupport φ) :
    ContinuousOn (fun t => ∫ x, φ x * v x t ∂μ) (Icc 0 S) ∧
      ∀ t ∈ Ioo 0 S,
        HasDerivAt (fun s => ∫ x, φ x * v x s ∂μ) (∫ x, φ x * deriv (v x) t ∂μ) t := by
  have hprod := smoothSpaceC1Time_mul (smoothSpaceC1Time_spatial_const hφ) hv
  have hsupp : ∀ x t, t ∈ Icc 0 S → x ∉ tsupport φ → φ x * v x t = 0 := by
    intro x t _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hh := c1_compact_mass_differentiation g μ hμ hprod hcφ hsupp
  refine ⟨hh.1, ?_⟩
  intro t ht
  have hvo : SmoothSpaceC1Time v (Ioo 0 S) :=
    ⟨fun s hs => hv.1 s (Ioo_subset_Icc_self hs),
      fun x => (hv.2 x).mono (Set.prod_mono (Subset.refl _) Ioo_subset_Icc_self)⟩
  have heq : (∫ x, deriv (fun s => φ x * v x s) t ∂μ) =
      ∫ x, φ x * deriv (v x) t ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => ((smoothSpaceC1Time_hasDerivAt isOpen_Ioo hvo x ht).const_mul (φ x)).deriv)
  rw [← heq]
  exact (hh.2 t ht).2.2

theorem cutoff_mass_initial_zero {n : ℕ} {M : ComplexManifold n}
    (μ : Measure M.Carrier) (v : M.Carrier → ℝ → ℝ) (φ : M.Carrier → ℝ)
    (hv : ∀ x, v x 0 = 0) : (∫ x, φ x * v x 0 ∂μ) = 0 := by
  simp only [hv, mul_zero, integral_zero]

end Yau.F04Proof
