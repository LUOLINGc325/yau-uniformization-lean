import Yau.LeafProofs.L14ModelExtension

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

theorem complexFormalAdjointTestRow_tsupport_subset {n : ℕ} {α β ι : Type*} [Fintype ι]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ) (r : β) (c : α) (ψ : ComplexVector n → ℝ) :
    tsupport (complexFormalAdjointTestRow v a b r c ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro z hz
  by_contra hn
  have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hn
  have hdψ : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  apply hz
  simp only [complexFormalAdjointTestRow, hψz, hdψ, ContinuousLinearMap.zero_apply,
    Complex.ofReal_zero, mul_zero, zero_add, Finset.sum_const_zero, neg_zero]

theorem complex_firstOrder_rows_components {n : ℕ} {α β ι : Type*} [Fintype α] [Fintype ι]
    (ν : Measure (ComplexVector n)) [IsLocallyFiniteMeasure ν]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiff ℝ ∞ (a r c i)) (hb : ∀ r c, ContDiff ℝ ∞ (b r c))
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hu : ∀ c, MemLp (fun z => u z c) 2 ν) (hw : ∀ r, MemLp (fun z => w z r) 2 ν)
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, (ψ z : ℂ) * w z r ∂ν) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂ν)
    (r : β) (q : Fin 2) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, ψ z * complexCoordinateCLM q (w z r) ∂ν) =
      ∫ z, ∑ c, complexCoordinateCLM q (u z c * complexFormalAdjointTestRow v a b r c ψ z) ∂ν := by
  have hψC : ContDiff ℝ ∞ (fun z => (ψ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hL : Integrable (fun z => (ψ z : ℂ) * w z r) ν := test_mul_integrable_of_memLp ν _ _
    (hψC.continuous.memLp_of_hasCompactSupport (hcψ.comp_left Complex.ofReal_zero)) (hw r)
  have hT (c : α) : Integrable (fun z => u z c * complexFormalAdjointTestRow v a b r c ψ z) ν := by
    have hθ : ContDiff ℝ ∞ (complexFormalAdjointTestRow v a b r c ψ) := by
      simpa only [contDiffOn_univ] using complexFormalAdjointTestRow_contDiffOn isOpen_univ v a b
        (fun r c i => (ha r c i).contDiffOn) (fun r c => (hb r c).contDiffOn) r c ψ hψ
    have hcθ : HasCompactSupport (complexFormalAdjointTestRow v a b r c ψ) :=
      hcψ.of_isClosed_subset (isClosed_tsupport _) (complexFormalAdjointTestRow_tsupport_subset v a b r c ψ)
    exact test_mul_integrable_of_memLp ν _ _ (hu c) (hθ.continuous.memLp_of_hasCompactSupport hcθ)
  have hR : Integrable (fun z => ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z) ν :=
    integrable_finsetSum _ (fun c _ => hT c)
  calc
    _ = ∫ z, complexCoordinateCLM q ((ψ z : ℂ) * w z r) ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simpa only [Complex.real_smul, smul_eq_mul] using
          ((complexCoordinateCLM q).map_smul (ψ z) (w z r)).symm
    _ = complexCoordinateCLM q (∫ z, (ψ z : ℂ) * w z r ∂ν) :=
      (complexCoordinateCLM q).integral_comp_comm hL
    _ = complexCoordinateCLM q (∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂ν) :=
      congrArg (complexCoordinateCLM q) (hrow r ψ hψ hcψ)
    _ = ∫ z, complexCoordinateCLM q (∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z) ∂ν :=
      ((complexCoordinateCLM q).integral_comp_comm hR).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun z => map_sum _ _ _)

end Yau.LeafProofs.L14Aux
