import Yau.Proofs.P03RegularizedCoefficientBounds
import Yau.Proofs.P03FinitePoleGerms
import Yau.Proofs.P03TopPushforwardAE

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The original intrinsic bounds give genuine Euclidean coefficient
estimates for a single pole on one fixed compact chart neighbourhood. -/
theorem exists_single_pole_coefficient_bound (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (pts : Finset M.Carrier)
    (b : ∀ p : pts, SmoothBumpFunction 𝓘(ℝ, ComplexVector n) p.1)
    (hs : ∀ p : pts, tsupport (b p : M.Carrier → ℝ) ⊆ {x | x ∈ pts ∧ x ≠ p.1}ᶜ)
    (m : ℕ) (u : NQForm E 0) (hu : LocallyL2 (r := r) E u) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j : ℕ, weightedNormSq (r := r) E g.form h μ
      (fun x => Φ x + finitePolePerturbation (fun p : pts => p.1) b m j x) u ≤ ENNReal.ofReal B)
    (p : pts) (α : Fin r) :
    ∃ R D : ℝ, 0 < R ∧ 0 ≤ D ∧
      Metric.closedBall (chartPt p.1 p.1) R ⊆ localDomain (r := r) E p.1 ∧
      ∀ j : ℕ, (∫⁻ z in Metric.closedBall (chartPt p.1 p.1) R,
        ENNReal.ofReal (‖coefficients (r := r) E u p.1 z Fin.elim0 α‖ ^ 2 *
          Real.exp (-((m : ℝ) * modelLogPole (chartPt p.1 p.1) (poleEpsilon j) z)))
          ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal D := by
  have hself : chartPt p.1 p.1 ∈ localDomain (r := r) E p.1 :=
    chartPt_mem_localDomain E p.1 p.1
      ⟨mem_extChartAt_source p.1, FiberBundle.mem_baseSet_trivializationAt' p.1⟩
  have hg := finitePole_single_germ pts b hs p (m : ℝ)
  have hn := inter_mem ((localDomain_isOpen E p.1).mem_nhds hself) hg
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hn
  let R := δ / 2
  let K := Metric.closedBall (chartPt p.1 p.1) R
  have hKR : K ⊆ Metric.ball (chartPt p.1 p.1) δ := fun z hz =>
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by dsimp [R]; linarith))
  have hK : K ⊆ localDomain (r := r) E p.1 := fun z hz => (hδs (hKR hz)).1
  obtain ⟨C, hC, hcoeff⟩ := exists_regularized_coefficient_bound E g μ hμ h hh Φ hΦ
    (finitePolePerturbation (fun p : pts => p.1) b m)
    (finitePolePerturbation_smooth _ b m) p.1 K (isCompact_closedBall _ _) hK α
  refine ⟨R, C * B, by dsimp [R]; positivity, mul_nonneg hC hB, hK, ?_⟩
  intro j
  have heq : (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u p.1 z Fin.elim0 α‖ ^ 2 *
        Real.exp (-((m : ℝ) * modelLogPole (chartPt p.1 p.1) (poleEpsilon j) z))) ∂lebesgueC n) =
      ∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u p.1 z Fin.elim0 α‖ ^ 2 *
        Real.exp (-finitePolePerturbation (fun p : pts => p.1) b m j (chartInv p.1 z))) ∂lebesgueC n := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
    rw [show finitePolePerturbation (fun p : pts => p.1) b m j (chartInv p.1 z) =
      (m : ℝ) * modelLogPole (chartPt p.1 p.1) (poleEpsilon j) z from
        (hδs (hKR hz)).2 (poleEpsilon j)]
  rw [← actualMeasure_eq_volume n]
  change (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u p.1 z Fin.elim0 α‖ ^ 2 *
    Real.exp (-((m : ℝ) * modelLogPole (chartPt p.1 p.1) (poleEpsilon j) z))) ∂lebesgueC n) ≤ _
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ
        (fun x => Φ x + finitePolePerturbation (fun p : pts => p.1) b m j x) u := hcoeff u hu j
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal B := mul_le_mul_right (hb j) _
    _ = _ := (ENNReal.ofReal_mul hC).symm

end Yau.NodeProofs.P03Aux
