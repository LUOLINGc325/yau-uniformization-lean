import Yau.Proofs.P06ScalarSmoothHeatDistribution
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Finitely many genuine coordinate word derivatives control the full
Fréchet derivative norm. The comparison constant depends only on the fixed
finite-dimensional basis and the derivative order. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem word_ofFn_eq_iteratedFDeriv (v : ι → E) {F : E → ℝ}
    (hF : ContDiff ℝ ∞ F) (j : ℕ) (p : Fin j → ι) (x : E) :
    regularityCoefficientWord v (List.ofFn p) F x =
      iteratedFDeriv ℝ j F x (fun a => v (p a)) := by
  induction j generalizing x with
  | zero => simp only [List.ofFn_zero,regularityCoefficientWord,iteratedFDeriv_zero_apply]
  | succ j ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (regularityCoefficientWord v (List.ofFn (fun a => p a.succ)) F) x (v (p 0)) = _
    have he : regularityCoefficientWord v (List.ofFn (fun a => p a.succ)) F =
        fun y => iteratedFDeriv ℝ j F y (fun a => v (p a.succ)) := funext (fun y => ih _ y)
    rw [he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j F) x :=
      hF.contDiffAt.differentiableAt_iteratedFDeriv (m := j)
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
    exact (hd.iteratedFDeriv_succ_apply_left' (m := fun a => v (p a))).symm

def multilinearCoordinates [Fintype ι] (b : Basis ι ℝ E) (j : ℕ) :
    (E [×j]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin j → ι) → ℝ) where
  toFun L p := L (fun a => b (p a))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem multilinearCoordinates_injective [Fintype ι] (b : Basis ι ℝ E) (j : ℕ) :
    Function.Injective (multilinearCoordinates b j) := by
  intro L T h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin j => b)
  intro p
  exact congrFun h p

theorem exists_multilinearCoordinates_bound [Fintype ι] (b : Basis ι ℝ E) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : E [×j]→L[ℝ] ℝ,
      ‖L‖ ≤ C * ‖multilinearCoordinates b j L‖ := by
  let Q := multilinearCoordinates b j
  have hQ := multilinearCoordinates_injective b j
  letI : FiniteDimensional ℝ (E [×j]→L[ℝ] ℝ) := FiniteDimensional.of_injective Q hQ
  obtain ⟨C,hC,hbound⟩ := Q.injective_iff_antilipschitz.mp hQ
  refine ⟨C,by exact_mod_cast hC,?_⟩
  intro L
  exact ZeroHomClass.bound_of_antilipschitz Q hbound L

/-- Uniform smallness of all words of one fixed length gives uniform
smallness of the complete actual derivative tensor. -/
theorem iteratedFDeriv_norm_lt_of_words [Fintype ι] (b : Basis ι ℝ E) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : E → ℝ), ContDiff ℝ ∞ F →
      ∀ (δ : ℝ), 0 < δ → ∀ x,
      (∀ p : Fin j → ι, |regularityCoefficientWord b (List.ofFn p) F x| < δ) →
        ‖iteratedFDeriv ℝ j F x‖ < C * δ := by
  obtain ⟨C,hC,hbound⟩ := exists_multilinearCoordinates_bound b j
  refine ⟨C,hC,?_⟩
  intro F hF δ hδ x hw
  have hcoord : ‖multilinearCoordinates b j (iteratedFDeriv ℝ j F x)‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro p
    change |iteratedFDeriv ℝ j F x (fun a => b (p a))| < δ
    rw [← word_ofFn_eq_iteratedFDeriv b hF j p x]
    exact hw p
  exact (hbound _).trans_lt (mul_lt_mul_of_pos_left hcoord hC)

end Yau.NodeProofs.P06Aux.ScalarSmooth
