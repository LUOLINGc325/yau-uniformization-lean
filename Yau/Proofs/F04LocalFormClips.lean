import Yau.Proofs.F04LaplacianClips
import Yau.Proofs.F04PositiveContinuity
import Yau.Proofs.F04SmoothCompositionContinuity
import Yau.Proofs.F04DirichletCore

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual local Laplacian form has zero pairing between opposite smooth
 clips of the same supported core function. -/
theorem localCoreForm_smooth_clips_cross_zero
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (H : HermitianField M)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (hCore : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreEmbedding g μ hμ O f) (dirichletCoreEmbedding g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    {δ : ℝ} (hδ : 0 < δ) (f : dirichletCore g μ hμ O) :
    B (dirichletPositiveSmoothing g μ hμ O δ (-(dirichletCoreEmbedding g μ hμ O f)))
      (dirichletPositiveSmoothing g μ hμ O δ (dirichletCoreEmbedding g μ hμ O f)) = 0 := by
  have hn : -(dirichletCoreEmbedding g μ hμ O f) = dirichletCoreEmbedding g μ hμ O (-f) :=
    ((dirichletCoreEmbedding g μ hμ O).map_neg f).symm
  rw [hn]
  change B (dirichletPositiveSmoothing g μ hμ O δ (dirichletCoreToEnergy g μ hμ O (-f)))
    (dirichletPositiveSmoothing g μ hμ O δ (dirichletCoreToEnergy g μ hμ O f)) = 0
  unfold dirichletPositiveSmoothing
  rw [dirichletSmoothComp_core g hK μ hμ O hO, dirichletSmoothComp_core g hK μ hμ O hO]
  change B (dirichletCoreEmbedding g μ hμ O
      (smoothCompositionCore g μ hμ O (smoothPositive δ) (smoothPositive_contDiff δ) (smoothPositive_zero δ) (-f)))
    (dirichletCoreEmbedding g μ hμ O
      (smoothCompositionCore g μ hμ O (smoothPositive δ) (smoothPositive_contDiff δ) (smoothPositive_zero δ) f)) = 0
  rw [hCore]
  change -(∫ x in O, smoothPositive δ (f.val x) *
    laplacian H (fun y => smoothPositive δ (-f.val y)) x ∂μ) = 0
  simp only [laplacian_smoothPositive_cross_zero H hδ (continuous_of_smoothFn f.val.2.1),
    integral_zero, neg_zero]

/-- Strong convergence of the genuine smooth graph clips and continuity of
 the supported positive part pass the exact local identity to all energy
 elements. The form is the continuous extension of its actual Laplacian core. -/
theorem localCoreForm_posPart_cross_zero
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (H : HermitianField M)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (hCore : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreEmbedding g μ hμ O f) (dirichletCoreEmbedding g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (u : DirichletEnergy g μ hμ O) :
    B (dirichletPosPart g μ hμ O hO (-u)) (dirichletPosPart g μ hμ O hO u) = 0 := by
  let pos := dirichletPosPart g μ hμ O hO
  let E := dirichletCoreEmbedding g μ hμ O
  have hCoreCross (f : dirichletCore g μ hμ O) : B (pos (-(E f))) (pos (E f)) = 0 := by
    let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
    have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
    have hl : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hn := dirichletPositiveSmoothing_tendsto g hK μ hμ O hO (-(E f)) δ hδ hl
    have hp := dirichletPositiveSmoothing_tendsto g hK μ hμ O hO (E f) δ hδ hl
    have hBC : Continuous (fun p : DirichletEnergy g μ hμ O × DirichletEnergy g μ hμ O => B p.1 p.2) :=
      (B.continuous.comp continuous_fst).clm_apply continuous_snd
    have hlim := (hBC.tendsto _).comp (hn.prodMk_nhds hp)
    have hZero : ∀ j, B (dirichletPositiveSmoothing g μ hμ O (δ j) (-(E f)))
        (dirichletPositiveSmoothing g μ hμ O (δ j) (E f)) = 0 :=
      fun j => localCoreForm_smooth_clips_cross_zero g hK μ hμ O hO H B hCore (hδ j) f
    have hConst : Tendsto (fun j => B (dirichletPositiveSmoothing g μ hμ O (δ j) (-(E f)))
        (dirichletPositiveSmoothing g μ hμ O (δ j) (E f))) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_congr' (Eventually.of_forall hZero)).mpr tendsto_const_nhds
    exact tendsto_nhds_unique hlim hConst
  have hpos : Continuous pos := continuous_dirichletPosPart g hK μ hμ O hO
  have hClosed : IsClosed {v : DirichletEnergy g μ hμ O | B (pos (-v)) (pos v) = 0} :=
    isClosed_eq ((B.continuous.comp (hpos.comp continuous_neg)).clm_apply hpos) continuous_const
  have hSubset : range E ⊆ {v : DirichletEnergy g μ hμ O | B (pos (-v)) (pos v) = 0} := by
    rintro _ ⟨f, rfl⟩
    exact hCoreCross f
  exact (closure_minimal hSubset hClosed) (dirichletCoreEmbedding_denseRange g μ hμ O u)

end Yau.F04Proof
