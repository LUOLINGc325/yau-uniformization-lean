import Yau.Proofs.D02LimitIdentification

/-! Local finiteness of the actual large atoms supplies a genuine
punctured coordinate disc inside the regular domain. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem exists_regular_punctured_disc (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤)
    {z₀ : ℂ} (hz : z₀ ∈ ball (0 : ℂ) 1) :
    ∃ R : ℝ, 0 < R ∧ closedBall z₀ R ⊆ ball (0 : ℂ) 1 ∧
      {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < R} ⊆ regularPotentialDomain (ball (0 : ℂ) 1) μ := by
  obtain ⟨a, ha, haD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_ball.mem_nhds hz)
  let Z := concentrationAtoms (ball (0 : ℂ) 1) μ
  let T : Set ℂ := (closedBall z₀ a ∩ Z) \ {z₀}
  have hT : T.Finite := (concentrationAtoms_finite_on_compact μ hμ
    (isCompact_closedBall z₀ a) haD).sdiff
  have hzT : z₀ ∉ T := fun h => h.2 (mem_singleton z₀)
  have hn : ball z₀ a ∩ Tᶜ ∈ 𝓝 z₀ :=
    inter_mem (isOpen_ball.mem_nhds (mem_ball_self ha)) (hT.isClosed.isOpen_compl.mem_nhds hzT)
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  have hRD : closedBall z₀ R ⊆ ball (0 : ℂ) 1 :=
    fun z hz => haD (ball_subset_closedBall (hsub hz).1)
  refine ⟨R, hR, hRD, fun z hz => ?_⟩
  have hzR : z ∈ closedBall z₀ R := by simpa only [mem_closedBall, dist_eq_norm] using hz.2.le
  have hzD := hRD hzR
  refine ⟨hzD, lt_of_not_ge ?_⟩
  intro hmass
  apply (hsub hzR).2
  refine ⟨⟨ball_subset_closedBall (hsub hzR).1, hzD, hmass⟩, ?_⟩
  intro heq
  have heq' : z = z₀ := mem_singleton_iff.mp heq
  simpa only [heq', sub_self, norm_zero, lt_self_iff_false] using hz.1

theorem rescaledCurve_parameter_mem {O : Set ℂ} (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hnear : {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < R} ⊆ O)
    {z : ℂ} (hz : z ∈ puncturedUnitDisc) : z₀ + (R : ℂ) * z ∈ O := by
  apply hnear
  have heq : ‖z₀ + (R : ℂ) * z - z₀‖ = R * ‖z‖ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  change 0 < ‖z₀ + (R : ℂ) * z - z₀‖ ∧ ‖z₀ + (R : ℂ) * z - z₀‖ < R
  rw [heq]
  exact ⟨mul_pos hR hz.1, by nlinarith [hz.2]⟩

theorem rescaledCurve_contMDiffOn_punctured {n : ℕ} {M : ComplexManifold n}
    {O : Set ℂ} {f : ℂ → M.Carrier}
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O) (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hnear : {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < R} ⊆ O) :
    ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (rescaledCurve f z₀ R) puncturedUnitDisc := by
  have ha : ContDiff ℂ ∞ (fun z : ℂ => z₀ + (R : ℂ) * z) := by fun_prop
  exact hf.comp ha.contMDiff.contMDiffOn (fun z hz => rescaledCurve_parameter_mem z₀ hR hnear hz)

end Yau.NodeProofs.D02Aux
