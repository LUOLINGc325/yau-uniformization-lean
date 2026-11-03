import Yau.Proofs.F04LocalFormInclusion
import Yau.Proofs.F03ScalarL2Pairing
import Yau.Proofs.F04AdjointGlobal

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletCore_laplacian_scalarL2
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (H : HermitianField M) (hH : MetricSmooth H)
    (f : dirichletCore g μ hμ O) : ScalarL2 (μ.restrict O) (laplacian H f.val) := by
  let := riemannianVolume_locallyFinite g μ hμ
  have hc : HasCompactSupport (laplacian H f.val) := by
    apply HasCompactSupport.of_support_subset_isCompact f.val.2.2
    intro x hx
    by_contra hn
    exact hx (laplacian_zero_of_notMem_tsupport H f.val hn)
  exact (scalarL2_iff_memLp _ _).mpr
    (((continuous_of_smoothFn (Adjoint.smoothFn_laplacian H hH f.val.2.1)).memLp_of_hasCompactSupport hc).restrict O)

/-- The actual compact first-argument test identity extends to every genuine
 supported energy test by core density, with its actual L2 Laplacian. -/
theorem localCoreForm_completed_test
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (H : HermitianField M) (hH : MetricSmooth H)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (f : dirichletCore g μ hμ O) (v : DirichletEnergy g μ hμ O) :
    B (dirichletCoreToEnergy g μ hμ O f) v =
      -inner ℝ (scalarToLp (dirichletCore_laplacian_scalarL2 g μ hμ O H hH f))
        (dirichletL2 g μ hμ O v) := by
  let L := scalarToLp (dirichletCore_laplacian_scalarL2 g μ hμ O H hH f)
  have hCore (k : dirichletCore g μ hμ O) :
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O k) =
        -inner ℝ L (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O k)) := by
    rw [hB, dirichletL2_core_eq_scalarToLp g μ hμ O k (dirichletCore_scalarL2 g μ hμ O k)]
    dsimp only [L]
    rw [scalarToLp_inner]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm (k.val x) (laplacian H f.val x))
  obtain ⟨k, hk⟩ := exists_dirichletCore_tendsto g μ hμ O v
  have hLeft := ((B (dirichletCoreToEnergy g μ hμ O f)).continuous.tendsto v).comp hk
  have hC : Continuous (fun w : DirichletEnergy g μ hμ O => -inner ℝ L (dirichletL2 g μ hμ O w)) :=
    (continuous_const.inner (dirichletL2 g μ hμ O).continuous).neg
  have hRight := (hC.tendsto v).comp hk
  exact tendsto_nhds_unique hLeft
    (hRight.congr' (Eventually.of_forall (fun j => (hCore (k j)).symm)))

end Yau.F04Proof
