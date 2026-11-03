import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual third derivatives of Hilbert norm squares. No bound on the
zeroth scalar energy is asserted. -/

open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_thirdFDeriv_norm_sq_le {O : Set E} (hO : IsOpen O)
    {Q : E → H} (hQ : ContDiffOn ℝ 3 Q O) {z : E} (hz : z ∈ O) :
    ‖iteratedFDeriv ℝ 3 (fun x => ‖Q x‖ ^ 2) z‖ ≤
      2 * ‖Q z‖ * ‖iteratedFDeriv ℝ 3 Q z‖ +
        6 * ‖iteratedFDeriv ℝ 1 Q z‖ * ‖iteratedFDeriv ℝ 2 Q z‖ := by
  have hb := (innerSL ℝ (E := H)).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hQ hQ hO.uniqueDiffOn hz (by norm_num : (3 : ℕ∞ω) ≤ 3) (norm_innerSL_le (𝕜 := ℝ))
  have hpoint : ContDiffAt ℝ 3 Q z := hQ.contDiffAt (hO.mem_nhds hz)
  have heq (m : ℕ) (hm : m ≤ 3) :
      iteratedFDerivWithin ℝ m Q O z = iteratedFDeriv ℝ m Q z :=
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      (hpoint.of_le (by exact_mod_cast hm)) hz
  have hsq : iteratedFDerivWithin ℝ 3 (fun x => ‖Q x‖ ^ 2) O z =
      iteratedFDeriv ℝ 3 (fun x => ‖Q x‖ ^ 2) z :=
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn (hpoint.norm_sq ℝ) hz
  have hinner : (fun y => ((innerSL ℝ) (Q y)) (Q y)) = (fun y => ‖Q y‖ ^ 2) := by
    funext y
    exact real_inner_self_eq_norm_sq (Q y)
  rw [hinner] at hb
  norm_num [Finset.sum_range_succ] at hb
  rw [hsq, heq 0 (by omega), heq 1 (by omega), heq 2 (by omega), heq 3 (by omega),
    norm_iteratedFDeriv_zero] at hb
  nlinarith

theorem uniform_norm_thirdFDeriv_norm_sq_le {O : Set E} (hO : IsOpen O)
    {Q : E → H} (hQ : ContDiffOn ℝ 3 Q O) {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ z ∈ O, ∀ m ≤ 3, ‖iteratedFDeriv ℝ m Q z‖ ≤ B) :
    ContDiffOn ℝ 3 (fun z => ‖Q z‖ ^ 2) O ∧
      ∀ z ∈ O, ‖iteratedFDeriv ℝ 3 (fun x => ‖Q x‖ ^ 2) z‖ ≤ 8 * B ^ 2 := by
  refine ⟨hQ.norm_sq ℝ, fun z hz => ?_⟩
  have h0 : ‖Q z‖ ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hjets z hz 0 (by omega)
  have h1 := hjets z hz 1 (by omega)
  have h2 := hjets z hz 2 (by omega)
  have h3 := hjets z hz 3 (by omega)
  have hb := norm_thirdFDeriv_norm_sq_le hO hQ hz
  have h03 := mul_le_mul h0 h3 (norm_nonneg _) hB
  have h12 := mul_le_mul h1 h2 (norm_nonneg _) hB
  nlinarith

end Yau.Blueprint.V02WallTaylorProof
