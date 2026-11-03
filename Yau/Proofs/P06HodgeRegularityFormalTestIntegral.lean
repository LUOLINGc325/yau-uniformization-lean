import Yau.Proofs.P06HodgeRegularityFormalCutoffData

/-! Integrability and integral expansion of the genuine divergence
formal transpose against an arbitrary actual L² representative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]

theorem regularityDivergenceFormal_test
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (C : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i)) (hC : ∀ r c, ContDiff ℝ ∞ (C r c))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (r c : α) :
    regularityTest O (fun z => divergenceFormalTest v a B C φ z r c) := by
  unfold divergenceFormalTest
  apply regularityTest_add
  · apply regularityTest_sub
    · apply regularityTest_neg
      apply regularityTest_sum
      intro i
      apply regularityTest_sum
      intro j
      apply regularityTest_add
      · exact regularityTest_coeff_mul
          (regularityTest_direction (regularityTest_direction hφ (v i)) (v j)) (ha r c i j)
      · exact regularityTest_coeff_mul (regularityTest_direction hφ (v i))
          (regularityDirection_contDiff (ha r c i j) (v j))
    · apply regularityTest_sum
      intro i
      exact regularityTest_coeff_mul (regularityTest_direction hφ (v i)) (hB r c i)
  · exact regularityTest_coeff_mul hφ (hC r c)

theorem regularityDivergenceFormal_integral
    (ν : Measure E) [IsLocallyFiniteMeasure ν]
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (C : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i)) (hC : ∀ r c, ContDiff ℝ ∞ (C r c))
    (U : E → α → ℝ) (hU : ∀ c, MemLp (fun z => U z c) 2 ν)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (r : α) :
    (∫ z, ∑ c, divergenceFormalTest v a B C φ z r c * U z c ∂ν) =
      ∑ c, ((∑ i, ∑ j, -(∫ z,
        (a r c i j z * fderiv ℝ (fun y => fderiv ℝ φ y (v i)) z (v j) +
          fderiv ℝ (a r c i j) z (v j) * fderiv ℝ φ z (v i)) * U z c ∂ν)) +
        (∑ i, -(∫ z, (B r c i z * fderiv ℝ φ z (v i)) * U z c ∂ν)) +
        ∫ z, φ z * (C r c z * U z c) ∂ν) := by
  have ht : regularityTest Set.univ φ := ⟨hφ,hcφ,Set.subset_univ _⟩
  apply integral_divergenceFormalTest ν v a B C U φ r
  · intro c i j
    have hp : regularityTest Set.univ (fun z =>
        a r c i j z * fderiv ℝ (fun y => fderiv ℝ φ y (v i)) z (v j) +
          fderiv ℝ (a r c i j) z (v j) * fderiv ℝ φ z (v i)) :=
      regularityTest_add
        (regularityTest_coeff_mul (regularityTest_direction (regularityTest_direction ht (v i)) (v j)) (ha r c i j))
        (regularityTest_coeff_mul (regularityTest_direction ht (v i))
          (regularityDirection_contDiff (ha r c i j) (v j)))
    have hpL : MemLp _ 2 ν := hp.1.continuous.memLp_of_hasCompactSupport hp.2.1
    exact hpL.integrable_mul (hU c)
  · intro c i
    have hb := regularityTest_coeff_mul (regularityTest_direction ht (v i)) (hB r c i)
    have hbL : MemLp _ 2 ν := hb.1.continuous.memLp_of_hasCompactSupport hb.2.1
    exact hbL.integrable_mul (hU c)
  · intro c
    have hc := regularityTest_mul ht (hC r c)
    have hcL : MemLp _ 2 ν := hc.1.continuous.memLp_of_hasCompactSupport hc.2.1
    exact (hcL.integrable_mul (hU c)).congr (Eventually.of_forall fun z => by
      dsimp only [Pi.mul_apply]
      ring)

end Yau.NodeProofs.P06Aux
