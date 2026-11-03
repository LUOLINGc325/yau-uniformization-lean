import Yau.Proofs.F01LinearCommutatorExpansion
import Yau.Proofs.F01HolderBilinear

/-! Numerical Holder control of the exact finite commutator forcing.
Only the coefficient words and the strictly lower solution Hessian words
in its proved expansion occur in the hypotheses. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem spatialDerivativeWord_append {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vs ws : List E) (u : E × ℝ → V) :
    spatialDerivativeWord (vs ++ ws) u =
      spatialDerivativeWord vs (spatialDerivativeWord ws u) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append, spatialDerivativeWord, ih]

theorem holderBound_list_sum_uniform {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (l : List ι)
    {Q : Set (Point n)} {β C : ℝ} (hC : 0 ≤ C) (f : ι → Point n → V)
    (hf : ∀ i ∈ l, HolderBound β Q (f i) C) :
    HolderBound β Q (fun p => (l.map (fun i => f i p)).sum) ((l.length : ℝ) * C) := by
  induction l with
  | nil =>
    refine ⟨by simp, ?_, ?_⟩ <;> simp
  | cons a l ih =>
    have ha := hf a (by simp)
    have hl := ih (fun i hi => hf i (by simp [hi]))
    have he : ((a :: l).length : ℝ) * C = C + (l.length : ℝ) * C := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    exact holderBound_add ha hl

local instance commutatorSourceBilinearNorm (n : ℕ) :
    Norm (Mat n →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

theorem linearCommutatorSource_holder
    (a : Point n → Mat n) (u f : Point n → ℝ)
    {Q : Set (Point n)} {S : Set (Space n)} {β Ca Cu Cf : ℝ}
    (hS : IsOpen S) (hQ : Q ⊆ S ×ˢ (Set.univ : Set ℝ))
    (ha : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => a (z, p.2)) S)
    (hu : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => u (z, p.2)) S)
    (hf : ∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S)
    (hCa : 0 ≤ Ca) (hCu : 0 ≤ Cu) (vs : List (Space n))
    (hF : HolderBound β Q (spatialDerivativeWord vs f) Cf)
    (hA : ∀ ab ∈ linearSpatialCommutatorPairs vs,
      HolderBound β Q (spatialDerivativeWord ab.1 a) Ca)
    (hH : ∀ ab ∈ linearSpatialCommutatorPairs vs,
      HolderBound β Q (spatialDD (spatialDerivativeWord ab.2 u)) Cu) :
    HolderBound β Q (linearCommutatorSource a u f vs)
      (Cf + ((linearSpatialCommutatorPairs vs).length : ℝ) *
        (2 * ‖realHessianContractionCLM (n := n)‖ * Ca * Cu)) := by
  let M : ℝ := 2 * ‖realHessianContractionCLM (n := n)‖ * Ca * Cu
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousLinearMap.opNorm_nonneg _)) hCa) hCu
  have hSum := holderBound_list_sum_uniform (linearSpatialCommutatorPairs vs) hM
    (fun ab p => realHessianContractionCLM (spatialDerivativeWord ab.1 a p)
      (spatialDD (spatialDerivativeWord ab.2 u) p))
    (fun ab hab => holderBound_bilinear (hA ab hab) (hH ab hab) realHessianContractionCLM)
  have hAdd := holderBound_add hF hSum
  have he : ∀ p ∈ Q, linearCommutatorSource a u f vs p =
      spatialDerivativeWord vs f p +
      ((linearSpatialCommutatorPairs vs).map (fun ab =>
        realHessianContractionCLM (spatialDerivativeWord ab.1 a p)
          (spatialDD (spatialDerivativeWord ab.2 u) p))).sum := by
    intro p hp
    exact linearCommutatorSource_expansion a u f hS (ha p hp) (hu p hp) (hf p hp) vs (hQ hp).1
  refine ⟨hAdd.1, ?_, ?_⟩
  · intro p hp
    change ‖linearCommutatorSource a u f vs p‖ ≤ _
    rw [he p hp]
    exact hAdd.2.1 p hp
  · intro p hp q hq
    change ‖linearCommutatorSource a u f vs p - linearCommutatorSource a u f vs q‖ ≤ _
    rw [he p hp, he q hq]
    exact hAdd.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
