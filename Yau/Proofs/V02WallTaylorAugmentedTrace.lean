import Yau.Proofs.V02WallTaylorCompactCoefficient
import Yau.Proofs.V03GagliardoVector

/-! Compact local intrinsic coefficient jets act on the actual boundary
half-order space. Auxiliary traces need only real continuity and periodicity. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {M : ComplexManifold n} {ι : Type*} [Fintype ι]

theorem augmentedJet_uniform_boundary_control
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K)
    {L : Set (EuclideanSpace ℂ ι)} (hL : IsCompact L) (m : ℕ)
    {B : CotangentPoint M → EuclideanSpace ℂ ι → ℂ [×m]→L[ℝ] ℂ}
    (hB : ∀ y ∈ K, ∀ p ∈ L,
      ContDiffAt ℝ 1 (fun w : CotangentCoord n × EuclideanSpace ℂ ι =>
        B (cotangentChartInv y.1 w.1) w.2) (cotangentChart y.1 y, p)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ y : ℝ → CotangentPoint M, (∀ θ, y θ ∈ K) →
      ∀ p : ℝ → EuclideanSpace ℂ ι, (∀ θ, p θ ∈ L) →
      Continuous (fun θ => G (y θ)) → Continuous p →
      Function.Periodic (fun θ => G (y θ)) (2 * Real.pi) → Function.Periodic p (2 * Real.pi) →
      (∀ θ, ‖B (y θ) (p θ)‖ ≤ D) ∧
      ∀ v : Fin m → ℂ, boundaryDSq (fun θ (_ : Unit) => B (y θ) (p θ) v) ≤
        ENNReal.ofReal (C * (∏ i, ‖v i‖) ^ 2) *
          (boundaryDSq (fun θ k => G (y θ) k) + boundaryDSq (fun θ k => p θ k)) := by
  obtain ⟨C, D, hC, hD, hsup, hdiff⟩ := augmentedCoefficient_compact_control hG hK hL hB
  refine ⟨2 * C ^ 2, D, by positivity, hD, fun y hy p hp hGc hpc hGp hpp => ?_⟩
  have hcoeff : Continuous (fun θ => B (y θ) (p θ)) := by
    let P : ℝ → (G '' K) × L := fun θ => (⟨G (y θ), ⟨y θ, hy θ, rfl⟩⟩, ⟨p θ, hp θ⟩)
    have hP : Continuous P := (hGc.subtype_mk _).prodMk (hpc.subtype_mk _)
    have hh := (compactAugmentedCoefficient_locallyLipschitz hG hK hB).continuous.comp hP
    apply hh.congr
    intro θ
    dsimp [P, compactAugmentedCoefficient]
    rw [compactImmersionPoint_eq hG.2.1 _ (hy θ)]
  have hperiodic : Function.Periodic (fun θ => B (y θ) (p θ)) (2 * Real.pi) := by
    intro θ
    change B (y (θ + 2 * Real.pi)) (p (θ + 2 * Real.pi)) = B (y θ) (p θ)
    rw [hpp θ]
    have hyperiod : y (θ + 2 * Real.pi) = y θ := hG.2.1 (hGp θ)
    rw [hyperiod]
  refine ⟨fun θ => hsup _ (hy θ) _ (hp θ), fun v => ?_⟩
  let data : ℝ → (Fin q ⊕ ι) → ℂ := fun θ => Sum.elim (fun k => G (y θ) k) (fun k => p θ k)
  have hdata (i : Fin q ⊕ ι) : Continuous (fun θ => data θ i) := by
    cases i with
    | inl k => exact (PiLp.continuous_apply 2 (fun _ : Fin q => ℂ) k).comp hGc
    | inr k => exact (PiLp.continuous_apply 2 (fun _ : ι => ℂ) k).comp hpc
  have hdatap (i : Fin q ⊕ ι) : Function.Periodic (fun θ => data θ i) (2 * Real.pi) := by
    cases i with
    | inl k => exact fun θ => congrArg (fun u : ComplexVector q => u k) (hGp θ)
    | inr k => exact fun θ => congrArg (fun u : EuclideanSpace ℂ ι => u k) (hpp θ)
  have hvalue : Continuous (fun θ => B (y θ) (p θ) v) :=
    continuous_eval.comp (hcoeff.prodMk continuous_const)
  have hDSq := boundaryDSq_le_of_sum_square_bound hdata hvalue hdatap
    (fun θ => congrArg (fun A : ℂ [×m]→L[ℝ] ℂ => A v) (hperiodic θ))
    (show 0 ≤ (2 * C ^ 2) * (∏ i, ‖v i‖) ^ 2 by positivity) (fun θ τ => ?_)
  · have heq : boundaryDSq data = boundaryDSq (fun θ k => G (y θ) k) +
        boundaryDSq (fun θ k => p θ k) := by
      simp only [boundaryDSq, Fintype.sum_sum_type, data, Sum.elim_inl, Sum.elim_inr]
    exact hDSq.trans_eq (by rw [heq])
  have hb := hdiff _ (hy θ) _ (hy τ) _ (hp θ) _ (hp τ)
  have heval : ‖B (y θ) (p θ) v - B (y τ) (p τ) v‖ ≤
      C * (‖G (y θ) - G (y τ)‖ + ‖p θ - p τ‖) * ∏ i, ‖v i‖ := by
    rw [← ContinuousMultilinearMap.sub_apply]
    exact (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
  have heval2 := mul_self_le_mul_self (norm_nonneg _) heval
  have hGsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => ℂ) (G (y θ) - G (y τ))
  have hpsq := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (p θ - p τ)
  have hsum : ∑ i, ‖data θ i - data τ i‖ ^ 2 =
      ‖G (y θ) - G (y τ)‖ ^ 2 + ‖p θ - p τ‖ ^ 2 := by
    rw [hGsq, hpsq]
    simp only [Fintype.sum_sum_type, data, Sum.elim_inl, Sum.elim_inr, PiLp.sub_apply]
  rw [hsum]
  have hscalar : (C * (‖G (y θ) - G (y τ)‖ + ‖p θ - p τ‖) * ∏ i, ‖v i‖) ^ 2 ≤
      (2 * C ^ 2) * (∏ i, ‖v i‖) ^ 2 *
        (‖G (y θ) - G (y τ)‖ ^ 2 + ‖p θ - p τ‖ ^ 2) := by
    have hh : (‖G (y θ) - G (y τ)‖ + ‖p θ - p τ‖) ^ 2 ≤
        2 * (‖G (y θ) - G (y τ)‖ ^ 2 + ‖p θ - p τ‖ ^ 2) := by nlinarith [sq_nonneg (‖G (y θ) - G (y τ)‖ - ‖p θ - p τ‖)]
    have hh' := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ C ^ 2 * (∏ i, ‖v i‖) ^ 2 by positivity)
    nlinarith
  nlinarith

end Yau.Blueprint.V02WallTaylorProof
