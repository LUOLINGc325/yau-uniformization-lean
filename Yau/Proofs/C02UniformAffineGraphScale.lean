import Yau.Proofs.C02AffinePrecompositionJets
import Yau.Proofs.C02FiniteJetEnvelope
import Yau.LeafProofs.L21Normalization

/-! At each finite order, a scale is fixed before all graph fields and
centres. It normalizes high jets without changing the chosen global chart. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L21Aux
variable {n : ℕ}

theorem exists_uniform_affine_graph_scale (n q : ℕ) (K : ℕ → ℝ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 8 ∧
      ∀ A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ,
      MatrixSmoothOn A (Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k, ‖A x i k‖ ≤ 1) →
      (∀ j, 1 ≤ j → ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k,
        ‖iteratedFDeriv ℝ j (fun y => A y i k) x‖ ≤ K j) →
      ∀ a ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ),
      MapsTo (fun z => a + s • z) (Metric.ball (0 : ComplexVector n) 1)
        (Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) ∧
      MatrixSmoothOn (fun z => A (a + s • z)) (Metric.ball (0 : ComplexVector n) 1) ∧
      JetBound q 1 (fun z => A (a + s • z)) (Metric.ball (0 : ComplexVector n) 1) := by
  let B := finiteJetEnvelope K q
  have hB : 1 ≤ B := finiteJetEnvelope_one_le K q
  let s := min (1 / 8 : ℝ) (1 / (B + 1))
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs8 : s ≤ 1 / 8 := min_le_left _ _
  have hs1 : s ≤ 1 := by linarith
  have hsB : B * s ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < B + 1)).mp (min_le_right (1 / 8 : ℝ) (1 / (B + 1)))
    change s * (B + 1) ≤ 1 at h
    nlinarith
  refine ⟨s, hs, hs8, ?_⟩
  intro A hA hValue hJets a ha
  have hMaps : MapsTo (fun z => a + s • z) (Metric.ball (0 : ComplexVector n) 1)
      (Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) := by
    intro z hz
    have haN : ‖a‖ < (1 / 4 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    have hzN : ‖z‖ < (1 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [Metric.mem_ball, dist_zero_right]
    have h := norm_add_le a (s • z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at h
    nlinarith
  refine ⟨hMaps, ?_, ?_⟩
  · intro i k
    exact (hA i k).comp (contDiff_const.add (contDiff_id.const_smul s)).contDiffOn hMaps
  · intro j hj x hx i k
    by_cases hj0 : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      exact hValue _ (hMaps hx) i k
    · have hPower : s ^ j ≤ s := by
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        rw [pow_succ]
        exact mul_le_of_le_one_left hs.le (pow_le_one₀ hs.le hs1)
      calc
        _ ≤ ‖iteratedFDeriv ℝ j (fun y => A y i k) (a + s • x)‖ * |s| ^ j :=
          norm_iteratedFDeriv_comp_affineOn_le Metric.isOpen_ball (hA i k) a s x (hMaps hx) j
        _ ≤ B * s ^ j := by
          rw [abs_of_pos hs]
          exact mul_le_mul_of_nonneg_right
            ((hJets j (by omega) _ (hMaps hx) i k).trans (le_finiteJetEnvelope K hj))
            (pow_nonneg hs.le j)
        _ ≤ B * s := mul_le_mul_of_nonneg_left hPower (by linarith)
        _ ≤ 1 := hsB

end Yau.Blueprint.C02Proof
