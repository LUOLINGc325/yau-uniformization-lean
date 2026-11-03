import Yau.Proofs.C02QuantitativeInverseSmooth
import Yau.Proofs.C02LocalInverseJetBounds
import Yau.Proofs.C02InverseMapJets

/-! One profile precedes every near-identity map with the prescribed
positive-order jet bounds, and controls its actual fixed-radius inverse. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance qij_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance qij_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

theorem exists_uniform_fixed_ball_inverse_jet_bounds (R : ℝ) (hR : 0 < R) (b : ℕ → ℝ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ f : E → E, ContDiff ℝ ∞ f →
      (∀ x ∈ Metric.ball (0 : E) R, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) →
      (∀ m, 1 ≤ m → ∀ x ∈ Metric.ball (0 : E) R, ‖iteratedFDeriv ℝ m f x‖ ≤ b m) →
      ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧
        e.source = Metric.ball (0 : E) R ∧
        Metric.closedBall (f 0) (3 * R / 8) ⊆ e.target ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        ∀ m y, y ∈ e.target → ‖iteratedFDeriv ℝ m e.symm y‖ ≤ B m := by
  let β := fun m => |b (m + 1)|
  let c := inverseJetMajorant β
  refine ⟨inverseMapJetMajorant c R, inverseMapJetMajorant_nonnegative c R, ?_⟩
  intro f hf hClose hJets
  obtain ⟨e, he, hSource, hTarget, heSmooth, heDeriv⟩ :=
    exists_fixed_ball_smooth_inverse f R hR hf hClose
  let V := Metric.ball (0 : E) R
  let D := fderiv ℝ f
  let C := fun x => (D x).inverse
  have hD : ContDiffOn ℝ ∞ D V := (hf.fderiv_right (by simp)).contDiffOn
  have hInv (x : E) (hx : x ∈ V) : (D x).IsInvertible :=
    isInvertible_of_close_identity (D x) (hClose x hx)
  have hC : ContDiffOn ℝ ∞ C V := by
    intro x hx
    exact ((hInv x hx).contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt x (hD x hx)
  have hBack : MapsTo e.symm e.target V := by
    intro y hy
    change e.symm y ∈ Metric.ball (0 : E) R
    rw [← hSource]
    exact e.map_target hy
  have hCBound (m : ℕ) (x : E) (hx : x ∈ V) : ‖iteratedFDeriv ℝ m C x‖ ≤ c m := by
    apply actualInverseField_jet_majorant_on Metric.isOpen_ball hD hInv hx β
      (fun i => abs_nonneg _) _ (norm_actual_inverse_of_close_identity (D x) (hClose x hx)) m
    intro i
    rw [norm_iteratedFDeriv_fderiv]
    exact (hJets (i + 1) (by omega) x hx).trans (le_abs_self _)
  refine ⟨e, he, hSource, hTarget, heSmooth, ?_⟩
  intro m y hy
  apply inverseCoordinateMap_jet_norm_le e.open_target Metric.isOpen_ball heSmooth hC
    hBack (fun z hz => (heDeriv z hz).1) c hCBound hy R _ m
  have hp := hBack hy
  have hPos : ‖e.symm y‖ < R := by simpa only [V, Metric.mem_ball, dist_zero_right] using hp
  exact hPos.le

end Yau.Blueprint.C02Proof
