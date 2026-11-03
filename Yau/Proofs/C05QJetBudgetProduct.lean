import Yau.Proofs.C05TensorProductDerivativeNorm

/-! The four genuine second covariant product terms have their exact intrinsic norms. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.Proofs.C05QJetBudgetAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L23Aux
variable {n r s : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def productLL (A : CovTensor n (r+1+1)) (B : CovTensor n s) : CovTensor n (r+s+1+1) :=
  fun v => tensorConcatProduct (fun u => A (Fin.cons (v 0) (Fin.cons (v 1) u))) B
    (fun j => v j.succ.succ)
def productLR (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) : CovTensor n (r+s+1+1) :=
  fun v => tensorConcatProduct (fun u => A (Fin.cons (v 1) u))
    (fun u => B (Fin.cons (v 0) u)) (fun j => v j.succ.succ)
def productRL (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) : CovTensor n (r+s+1+1) :=
  fun v => tensorConcatProduct (fun u => A (Fin.cons (v 0) u))
    (fun u => B (Fin.cons (v 1) u)) (fun j => v j.succ.succ)
def productRR (A : CovTensor n r) (B : CovTensor n (s+1+1)) : CovTensor n (r+s+1+1) :=
  fun v => tensorConcatProduct A (fun u => B (Fin.cons (v 0) (Fin.cons (v 1) u)))
    (fun j => v j.succ.succ)

theorem covTensorPair_two (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n (r+1+1)) :
    covTensorPair G A B = ∑ i, ∑ j, ∑ a, ∑ b, G⁻¹ i j * G⁻¹ a b *
      covTensorPair G (fun u => A (Fin.cons i (Fin.cons a u)))
        (fun u => B (Fin.cons j (Fin.cons b u))) := by
  rw [covTensorPair_succ]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covTensorPair_succ]
  simp only [Finset.mul_sum,mul_assoc]

theorem productLL_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n (r+1+1)) (B : CovTensor n (s)) :
    covTensorNormSq G (productLL A B)=covTensorNormSq G A*covTensorNormSq G B := by
  change covTensorPair G (productLL A B) (productLL A B)=covTensorPair G A A*covTensorPair G B B
  rw [covTensorPair_two]
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n,
        G⁻¹ i j*G⁻¹ a b*(covTensorPair G (fun u => A (Fin.cons i (Fin.cons a u))) (fun u => A (Fin.cons j (Fin.cons b u))) * covTensorPair G B B) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change G⁻¹ i j*G⁻¹ a b*covTensorPair G _ _ = _
      simp only [productLL,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
      rw [covTensorPair_concatProduct]
    _ = (∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n, G⁻¹ i j*G⁻¹ a b*covTensorPair G (fun u => A (Fin.cons i (Fin.cons a u))) (fun u => A (Fin.cons j (Fin.cons b u)))) * covTensorPair G B B := by
      simp only [Finset.sum_mul,mul_assoc]
    _ = _ := by rw [←covTensorPair_two]

theorem productRR_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n (r)) (B : CovTensor n (s+1+1)) :
    covTensorNormSq G (productRR A B)=covTensorNormSq G A*covTensorNormSq G B := by
  change covTensorPair G (productRR A B) (productRR A B)=covTensorPair G A A*covTensorPair G B B
  rw [covTensorPair_two]
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n,
        G⁻¹ i j*G⁻¹ a b*(covTensorPair G A A * covTensorPair G (fun u => B (Fin.cons i (Fin.cons a u))) (fun u => B (Fin.cons j (Fin.cons b u)))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change G⁻¹ i j*G⁻¹ a b*covTensorPair G _ _ = _
      simp only [productRR,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
      rw [covTensorPair_concatProduct]
    _ = covTensorPair G A A * (∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n, G⁻¹ i j*G⁻¹ a b*covTensorPair G (fun u => B (Fin.cons i (Fin.cons a u))) (fun u => B (Fin.cons j (Fin.cons b u)))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [←covTensorPair_two]

theorem productLR_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) :
    covTensorNormSq G (productLR A B)=covTensorNormSq G A*covTensorNormSq G B := by
  change covTensorPair G (productLR A B) (productLR A B)=covTensorPair G A A*covTensorPair G B B
  rw [covTensorPair_two]
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n,
        G⁻¹ i j*G⁻¹ a b*(covTensorPair G (fun u => A (Fin.cons a u)) (fun u => A (Fin.cons b u)) * covTensorPair G (fun u => B (Fin.cons i u)) (fun u => B (Fin.cons j u))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change G⁻¹ i j*G⁻¹ a b*covTensorPair G _ _ = _
      simp only [productLR,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
      rw [covTensorPair_concatProduct]
    _ = (∑ a : RIdx n, ∑ b : RIdx n, G⁻¹ a b*covTensorPair G (fun u => A (Fin.cons a u)) (fun u => A (Fin.cons b u))) * (∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j*covTensorPair G (fun u => B (Fin.cons i u)) (fun u => B (Fin.cons j u))) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := congrArg₂ (· * ·) (covTensorPair_succ G A A).symm (covTensorPair_succ G B B).symm

theorem productRL_normSq (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) :
    covTensorNormSq G (productRL A B)=covTensorNormSq G A*covTensorNormSq G B := by
  change covTensorPair G (productRL A B) (productRL A B)=covTensorPair G A A*covTensorPair G B B
  rw [covTensorPair_two]
  calc
    _ = ∑ i : RIdx n, ∑ j : RIdx n, ∑ a : RIdx n, ∑ b : RIdx n,
        G⁻¹ i j*G⁻¹ a b*(covTensorPair G (fun u => A (Fin.cons i u)) (fun u => A (Fin.cons j u)) * covTensorPair G (fun u => B (Fin.cons a u)) (fun u => B (Fin.cons b u))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change G⁻¹ i j*G⁻¹ a b*covTensorPair G _ _ = _
      simp only [productRL,Fin.cons_zero,Fin.cons_one,Fin.cons_succ]
      rw [covTensorPair_concatProduct]
    _ = (∑ i : RIdx n, ∑ j : RIdx n, G⁻¹ i j*covTensorPair G (fun u => A (Fin.cons i u)) (fun u => A (Fin.cons j u))) * (∑ a : RIdx n, ∑ b : RIdx n, G⁻¹ a b*covTensorPair G (fun u => B (Fin.cons a u)) (fun u => B (Fin.cons b u))) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := congrArg₂ (· * ·) (covTensorPair_succ G A A).symm (covTensorPair_succ G B B).symm

theorem covariantD_twice_product_norm_le (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    Real.sqrt (covTensorNormSq G (covariantD k c
      (covariantD k c (fun w => tensorConcatProduct (A w) (B w))) z)) ≤
    Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c A) z))*
        Real.sqrt (covTensorNormSq G (B z)) +
      2*Real.sqrt (covTensorNormSq G (covariantD k c A z))*
        Real.sqrt (covTensorNormSq G (covariantD k c B z)) +
      Real.sqrt (covTensorNormSq G (A z))*
        Real.sqrt (covTensorNormSq G (covariantD k c (covariantD k c B) z)) := by
  let A₀ := A z
  let A₁ := covariantD k c A z
  let A₂ := covariantD k c (covariantD k c A) z
  let B₀ := B z
  let B₁ := covariantD k c B z
  let B₂ := covariantD k c (covariantD k c B) z
  have he : covariantD k c (covariantD k c (fun w => tensorConcatProduct (A w) (B w))) z =
      productLL A₂ B₀ + productLR A₁ B₁ + productRL A₁ B₁ + productRR A₀ B₂ := by
    funext v
    have hv : Fin.cons (v 0) (Fin.cons (v 1) (fun j => v j.succ.succ))=v := by
      funext j
      refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun _ => rfl) j
    have hh := covariantD_twice_concatProduct k hk c A B hA hB hz
      (v 0) (v 1) (fun j => v j.succ.succ)
    rw [hv] at hh
    exact hh
  rw [he]
  have h1 := sqrt_covTensorNormSq_add_le G hG (productLL A₂ B₀) (productLR A₁ B₁)
  have h2 := sqrt_covTensorNormSq_add_le G hG (productLL A₂ B₀+productLR A₁ B₁) (productRL A₁ B₁)
  have h3 := sqrt_covTensorNormSq_add_le G hG
    (productLL A₂ B₀+productLR A₁ B₁+productRL A₁ B₁) (productRR A₀ B₂)
  have hsum := h3.trans (add_le_add (h2.trans
    (add_le_add h1 (le_refl _))) (le_refl _))
  rw [productLL_normSq,productLR_normSq,productRL_normSq,productRR_normSq] at hsum
  rw [Real.sqrt_mul (covTensorNormSq_nonneg G hG A₂),
    Real.sqrt_mul (covTensorNormSq_nonneg G hG A₁),
    Real.sqrt_mul (covTensorNormSq_nonneg G hG A₀)] at hsum
  exact hsum.trans_eq (by dsimp only [A₀,A₁,A₂,B₀,B₁,B₂]; ring)

end Yau.Proofs.C05QJetBudgetAux
