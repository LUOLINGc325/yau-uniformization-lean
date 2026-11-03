import Yau.Proofs.V02WallTaylorDirichletJets
import Yau.Proofs.V02WallTaylorHilbert

/-! Uniform third jets of the actual Fourier seminorm use only its initial
energy and the increment jets. No bound on the trace mean is imposed. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

theorem actual_traceEnergy_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) :
    ContDiffOn ℝ ∞ (fun z => (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal) U := by
  have hh := (angularDirichletVector_contDiffOn hU hf).norm_sq ℝ
  exact hh.congr (fun z hz => (angularDirichletVector_norm_sq hU hf hz (hp z hz)).symm)

theorem uniform_actual_traceEnergy_third_le {U : Set ℂ} (hU : IsOpen U) (h0U : 0 ∈ U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {E0 B0 B : ℝ} (hE0 : 0 ≤ E0) (hB0 : 0 ≤ B0) (hB : 0 ≤ B)
    (hinit : boundaryDSq (fun θ (_ : Unit) => f (0, θ)) ≤ ENNReal.ofReal E0)
    (hincrement : ∀ z ∈ U, boundaryDSq (fun θ (_ : Unit) => f (z, θ) - f (0, θ)) ≤
      ENNReal.ofReal (B0 ^ 2))
    (hjets : ∀ z ∈ U, ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ v : Fin m → ℂ,
      boundaryDSq (fun θ (_ : Unit) => iteratedFDeriv ℝ m (fun p => f (p, θ)) z v) ≤
        ENNReal.ofReal ((B * ∏ i, ‖v i‖) ^ 2)) :
    ∀ z ∈ U, ‖iteratedFDeriv ℝ 3
      (fun p => (boundaryDSq (fun θ (_ : Unit) => f (p, θ))).toReal) z‖ ≤
      2 * (Real.sqrt E0 + B0) * B + 6 * B ^ 2 := by
  intro z hz
  let Q := angularDirichletVector hU hf
  have hQ : ContDiffOn ℝ 3 Q U := (angularDirichletVector_contDiffOn hU hf).of_le (by simp)
  have he : (fun p => (boundaryDSq (fun θ (_ : Unit) => f (p, θ))).toReal) =ᶠ[𝓝 z]
      (fun p => ‖Q p‖ ^ 2) := by
    filter_upwards [hU.mem_nhds hz] with p hpU
    exact (angularDirichletVector_norm_sq hU hf hpU (hp p hpU)).symm
  rw [(he.iteratedFDeriv (𝕜 := ℝ) 3).eq_of_nhds]
  have h0fin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hinit
  have hdifffin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hincrement z hz)
  have htriangle := boundaryDSq_sqrt_add_le
    (parameter_angle_slice_contDiff hf h0U).continuous
    ((parameter_angle_slice_contDiff hf hz).continuous.sub
      (parameter_angle_slice_contDiff hf h0U).continuous) h0fin hdifffin
  simp only [Pi.sub_apply] at htriangle
  have hsum : (fun θ (_ : Unit) => f (0, θ) + (f (z, θ) - f (0, θ))) =
      (fun θ (_ : Unit) => f (z, θ)) := by
    funext θ k; ring
  rw [hsum] at htriangle
  have hQnorm : ‖Q z‖ = Real.sqrt (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal := by
    rw [← angularDirichletVector_norm_sq hU hf hz (hp z hz), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  have hinitial := Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal hE0 hinit)
  have hincr := Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (hincrement z hz))
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB0] at hincr
  have hvalue : ‖Q z‖ ≤ Real.sqrt E0 + B0 := by rw [hQnorm]; linarith
  have h1 : ‖iteratedFDeriv ℝ 1 Q z‖ ≤ B :=
    norm_iteratedFDeriv_angularDirichletVector_le hU hf hp 1 hz hB (hjets z hz 1 (by omega) (by omega))
  have h2 : ‖iteratedFDeriv ℝ 2 Q z‖ ≤ B :=
    norm_iteratedFDeriv_angularDirichletVector_le hU hf hp 2 hz hB (hjets z hz 2 (by omega) (by omega))
  have h3 : ‖iteratedFDeriv ℝ 3 Q z‖ ≤ B :=
    norm_iteratedFDeriv_angularDirichletVector_le hU hf hp 3 hz hB (hjets z hz 3 (by omega) (by omega))
  have hb := norm_thirdFDeriv_norm_sq_le hU hQ hz
  have h03 := mul_le_mul hvalue h3 (norm_nonneg _) (add_nonneg (Real.sqrt_nonneg _) hB0)
  have h12 := mul_le_mul h1 h2 (norm_nonneg _) hB
  nlinarith

end Yau.Blueprint.V02WallTaylorProof
