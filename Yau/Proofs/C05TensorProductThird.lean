import Yau.Proofs.C05TensorProductThirdProducts

/-! Eight genuine third covariant product terms and their exact intrinsic bound. -/
noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05TensorProductThirdAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05QJetBudgetAux Yau.LeafProofs.L23Aux
variable {n r s : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem second_product_eq (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun w => B w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (covariantD k c (fun w => tensorConcatProduct (A w) (B w))) z =
      productLL (covariantD k c (covariantD k c A) z) (B z) +
      productLR (covariantD k c A z) (covariantD k c B z) +
      productRL (covariantD k c A z) (covariantD k c B z) +
      productRR (A z) (covariantD k c (covariantD k c B) z) := by
  funext v
  have hv : Fin.cons (v 0) (Fin.cons (v 1) (fun j => v j.succ.succ)) = v := by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun _ => rfl) j
  have H := covariantD_twice_concatProduct k hk c A B hA hB hz
    (v 0) (v 1) (fun j => v j.succ.succ)
  rw [hv] at H
  exact H

theorem covariantD_thrice_product_norm_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun w => A w v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun w => B w v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    Real.sqrt (covTensorNormSq G
      (covariantD k c (covariantD k c (covariantD k c
        (fun w => tensorConcatProduct (A w) (B w)))) z)) ≤
      Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c (covariantD k c A)) z)) *
        Real.sqrt (covTensorNormSq G (B z)) +
      3 * Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c A) z)) *
        Real.sqrt (covTensorNormSq G (covariantD k c B z)) +
      3 * Real.sqrt (covTensorNormSq G (covariantD k c A z)) *
        Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c B) z)) +
      Real.sqrt (covTensorNormSq G (A z)) *
        Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c (covariantD k c B)) z)) := by
  let P := fun w => tensorConcatProduct (A w) (B w)
  let F₁ := fun w => productLL (covariantD k c (covariantD k c A) w) (B w)
  let F₂ := fun w => productLR (covariantD k c A w) (covariantD k c B w)
  let F₃ := fun w => productRL (covariantD k c A w) (covariantD k c B w)
  let F₄ := fun w => productRR (A w) (covariantD k c (covariantD k c B) w)
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hDA := covariantD_contDiffOn k hk c A hA
  have hDB := covariantD_contDiffOn k hk c B hB
  have hDDA := covariantD_contDiffOn k hk c (covariantD k c A) hDA
  have hDDB := covariantD_contDiffOn k hk c (covariantD k c B) hDB
  have hdA v := ((hA v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdB v := ((hB v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdDA v := ((hDA v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdDB v := ((hDB v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdDDA v := ((hDDA v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdDDB v := ((hDDB v).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have d₁ v : DifferentiableAt ℝ (fun w => F₁ w v) z := by
    dsimp only [F₁,productLL,tensorConcatProduct]
    exact (hdDDA _).mul (hdB _)
  have d₂ v : DifferentiableAt ℝ (fun w => F₂ w v) z := by
    dsimp only [F₂,productLR,tensorConcatProduct]
    exact (hdDA _).mul (hdDB _)
  have d₃ v : DifferentiableAt ℝ (fun w => F₃ w v) z := by
    dsimp only [F₃,productRL,tensorConcatProduct]
    exact (hdDA _).mul (hdDB _)
  have d₄ v : DifferentiableAt ℝ (fun w => F₄ w v) z := by
    dsimp only [F₄,productRR,tensorConcatProduct]
    exact (hdA _).mul (hdDDB _)
  have he : covariantD k c (covariantD k c P) =ᶠ[𝓝 z]
      (fun w => F₁ w + F₂ w + F₃ w + F₄ w) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact second_product_eq k hk c A B hA hB hw
  have hd := covariantD_eventuallyEq k c _ _ z he
  rw [covariantD_add_at k c (fun w => F₁ w + F₂ w + F₃ w) F₄ z (fun v => ((d₁ v).add (d₂ v)).add (d₃ v)) d₄,
    covariantD_add_at k c (fun w => F₁ w + F₂ w) F₃ z (fun v => (d₁ v).add (d₂ v)) d₃,
    covariantD_add_at k c F₁ F₂ z d₁ d₂] at hd
  have h₁ := covariantD_reindexed_product_norm_le k c (covariantD k c (covariantD k c A)) B
    (slotsLL r s) z G hG hdDDA hdB
  have h₂ := covariantD_reindexed_product_norm_le k c (covariantD k c A) (covariantD k c B)
    (slotsLR r s) z G hG hdDA hdDB
  have h₃ := covariantD_reindexed_product_norm_le k c (covariantD k c A) (covariantD k c B)
    (slotsRL r s) z G hG hdDA hdDB
  have h₄ := covariantD_reindexed_product_norm_le k c A (covariantD k c (covariantD k c B))
    (slotsRR r s) z G hG hdA hdDDB
  have e₁ : F₁ = (fun w v => tensorConcatProduct (covariantD k c (covariantD k c A) w) (B w)
      (v ∘ slotsLL r s)) := by funext w; exact productLL_reindex _ _
  have e₂ : F₂ = (fun w v => tensorConcatProduct (covariantD k c A w) (covariantD k c B w)
      (v ∘ slotsLR r s)) := by funext w; exact productLR_reindex _ _
  have e₃ : F₃ = (fun w v => tensorConcatProduct (covariantD k c A w) (covariantD k c B w)
      (v ∘ slotsRL r s)) := by funext w; exact productRL_reindex _ _
  have e₄ : F₄ = (fun w v => tensorConcatProduct (A w) (covariantD k c (covariantD k c B) w)
      (v ∘ slotsRR r s)) := by funext w; exact productRR_reindex _ _
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  rw [← e₃] at h₃
  rw [← e₄] at h₄
  have t₁ := sqrt_covTensorNormSq_add_le G hG (covariantD k c F₁ z) (covariantD k c F₂ z)
  have t₂ := sqrt_covTensorNormSq_add_le G hG
    (covariantD k c F₁ z + covariantD k c F₂ z) (covariantD k c F₃ z)
  have t₃ := sqrt_covTensorNormSq_add_le G hG
    (covariantD k c F₁ z + covariantD k c F₂ z + covariantD k c F₃ z) (covariantD k c F₄ z)
  have ht := t₃.trans (add_le_add (t₂.trans (add_le_add t₁ (le_refl _))) (le_refl _))
  have hsum := ht.trans (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄)
  change Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c (covariantD k c P)) z)) ≤ _
  rw [hd]
  exact hsum.trans_eq (by ring)

end Yau.Proofs.C05TensorProductThirdAux
