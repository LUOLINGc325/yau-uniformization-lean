import Yau.Proofs.F03DirichletInclusion
import Yau.Proofs.F04LocalFormMarkov

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletInclusion_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {O W : Set M.Carrier} (hOW : O ⊆ W)
    (f : dirichletCore g μ hμ O) :
    dirichletInclusion g μ hμ hOW (dirichletCoreToEnergy g μ hμ O f) =
      dirichletCoreToEnergy g μ hμ W ⟨f.val, f.property.trans hOW⟩ := by
  apply Subtype.ext
  rfl

/-- Two actual local forms agree under supported-domain inclusion, proved
 first on their genuine compact cores and then in the energy norm. -/
theorem localCoreForm_inclusion_eq
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O W : Set M.Carrier} (hOW : O ⊆ W) (H : HermitianField M)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (A : DirichletEnergy g μ hμ W →L[ℝ] DirichletEnergy g μ hμ W →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (hA : ∀ f v : dirichletCore g μ hμ W,
      A (dirichletCoreToEnergy g μ hμ W f) (dirichletCoreToEnergy g μ hμ W v) =
        -(∫ x in W, v.val x * laplacian H f.val x ∂μ))
    (u v : DirichletEnergy g μ hμ O) :
    B u v = A (dirichletInclusion g μ hμ hOW u) (dirichletInclusion g μ hμ hOW v) := by
  let I := dirichletInclusion g μ hμ hOW
  have hCore (f k : dirichletCore g μ hμ O) :
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O k) =
        A (I (dirichletCoreToEnergy g μ hμ O f)) (I (dirichletCoreToEnergy g μ hμ O k)) := by
    rw [hB, dirichletInclusion_core, dirichletInclusion_core, hA]
    have hInt (S : Set M.Carrier) (hOS : O ⊆ S) :
        (∫ x in S, k.val x * laplacian H f.val x ∂μ) = ∫ x, k.val x * laplacian H f.val x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn : x ∉ tsupport k.val := fun hk => hx (hOS (k.property hk))
      rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
    rw [hInt O Subset.rfl, hInt W hOW]
  obtain ⟨f, hf⟩ := exists_dirichletCore_tendsto g μ hμ O u
  obtain ⟨k, hk⟩ := exists_dirichletCore_tendsto g μ hμ O v
  have hBC : Continuous (fun p : DirichletEnergy g μ hμ O × DirichletEnergy g μ hμ O => B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  have hAC : Continuous (fun p : DirichletEnergy g μ hμ O × DirichletEnergy g μ hμ O => A (I p.1) (I p.2)) :=
    (A.continuous.comp (I.continuous.comp continuous_fst)).clm_apply (I.continuous.comp continuous_snd)
  have hLeft := (hBC.tendsto (u, v)).comp (hf.prodMk_nhds hk)
  have hRight := (hAC.tendsto (u, v)).comp (hf.prodMk_nhds hk)
  exact tendsto_nhds_unique hLeft
    (hRight.congr' (Eventually.of_forall (fun j => (hCore (f j) (k j)).symm)))

end Yau.F04Proof
