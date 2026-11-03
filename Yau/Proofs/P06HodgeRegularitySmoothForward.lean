import Yau.Proofs.P06HodgeRegularitySmoothTranspose

/-! Compact-test duality equals the original computed forward expression,
with the actual sign and unshifted source. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem regularityCompactTest_integral_add
    (φ : E → ℝ) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (f g : E → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z, φ z * (f z + g z) ∂ν) = (∫ z, φ z * f z ∂ν) + ∫ z, φ z * g z ∂ν := by
  simp only [mul_add]
  exact integral_add ((hφ.mul hf).integrable_of_hasCompactSupport hcφ.mul_right)
    ((hφ.mul hg).integrable_of_hasCompactSupport hcφ.mul_right)

theorem regularitySmoothForward_row
    (v : ι → E) (a : ι → ι → E → ℝ) (e1 : ι → E → ℝ) (e0 u : E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (he1 : ∀ i, ContDiff ℝ ∞ (e1 i)) (he0 : ContDiff ℝ ∞ e0) (hu : ContDiff ℝ ∞ u)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ z, φ z * (-(∑ i, ∑ j, a i j z * regularityDirection (v i) (regularityDirection (v j) u) z) +
      (∑ i, e1 i z * regularityDirection (v i) u z) + e0 z * u z) ∂ν) =
      -(∑ i, ∑ j, ∫ z, (a i j z * φ z) *
        regularityDirection (v i) (regularityDirection (v j) u) z ∂ν) +
      (∑ i, ∫ z, (e1 i z * φ z) * regularityDirection (v i) u z ∂ν) +
        ∫ z, u z * (e0 z * φ z) ∂ν := by
  have hQ i j := (ha i j).mul (regularityDirection_contDiff (regularityDirection_contDiff hu (v j)) (v i))
  have hR i := (he1 i).mul (regularityDirection_contDiff hu (v i))
  have hQS : ContDiff ℝ ∞ (fun z => ∑ i, ∑ j,
      a i j z * regularityDirection (v i) (regularityDirection (v j) u) z) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => hQ i j
  have hRS : ContDiff ℝ ∞ (fun z => ∑ i, e1 i z * regularityDirection (v i) u z) :=
    ContDiff.sum fun i _ => hR i
  rw [regularityCompactTest_integral_add ν φ hφ.continuous hcφ _ _
    (hQS.neg.add hRS).continuous (he0.mul hu).continuous,
    regularityCompactTest_integral_add ν φ hφ.continuous hcφ _ _ hQS.neg.continuous hRS.continuous]
  simp only [mul_neg, integral_neg]
  rw [DivergenceEnergy.test_sum ν φ hφ.continuous hcφ _
      (fun i => (ContDiff.sum fun j _ => hQ i j).continuous)]
  simp_rw [DivergenceEnergy.test_sum ν φ hφ.continuous hcφ _ (fun j => (hQ _ j).continuous)]
  rw [DivergenceEnergy.test_sum ν φ hφ.continuous hcφ _ (fun i => (hR i).continuous)]
  congr 2
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  · funext z
    ring

theorem regularitySmoothTranspose_principal
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (U : E → α → ℝ) (hU : ∀ c, ContDiff ℝ ∞ (fun z => U z c))
    (hUL : ∀ c, MemLp (fun z => U z c) 2 ν)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (r : α) :
    (∫ z, ∑ c, regularityForwardTranspose v a e1 e0 φ z r c * U z c ∂ν) =
      ∫ z, φ z * hodgeForwardPrincipal v a e1 e0 U z r ∂ν := by
  classical
  have htφ : regularityTest Set.univ φ := ⟨hφ,hcφ,Set.subset_univ _⟩
  have hrow c : Integrable (fun z => regularityForwardTranspose v a e1 e0 φ z r c * U z c) ν := by
    have ht := regularityForwardTranspose_test v a e1 e0 ha he1 he0 htφ r c
    have htL : MemLp _ 2 ν := ht.1.continuous.memLp_of_hasCompactSupport ht.2.1
    exact htL.integrable_mul (hUL c)
  rw [integral_finsetSum Finset.univ (fun c _ => hrow c)]
  unfold hodgeForwardPrincipal
  rw [DivergenceEnergy.test_sum ν φ hφ.continuous hcφ _ (fun c => by
    exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (ha r c i j).mul (regularityDirection_contDiff (regularityDirection_contDiff (hU c) (v j)) (v i))).neg.add
      (ContDiff.sum fun i _ => (he1 r c i).mul (regularityDirection_contDiff (hU c) (v i)))).add
        ((he0 r c).mul (hU c)) |>.continuous)]
  apply Finset.sum_congr rfl
  intro c _
  have hh := regularitySmoothTranspose_row ν v a e1 e0 ha he1 he0 (fun z => U z c) (hU c) (hUL c) hφ hcφ r c
  have heq : (∫ z, regularityForwardTranspose v a e1 e0 φ z r c * U z c ∂ν) =
      ∫ z, U z c * regularityForwardTranspose v a e1 e0 φ z r c ∂ν :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [heq,hh]
  exact (regularitySmoothForward_row ν v (a r c) (e1 r c) (e0 r c) (fun z => U z c)
    (ha r c) (he1 r c) (he0 r c) (hU c) hφ hcφ).symm

end Yau.NodeProofs.P06Aux
