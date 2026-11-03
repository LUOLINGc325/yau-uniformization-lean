import Yau.LeafProofs.L17FrozenHeatEquivalences
import Yau.LeafProofs.L16ParametrixBounds

/-! The actual frozen whole-space Gaussian solver and its uniform finite jet estimates. -/

noncomputable section

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def BoundedChartFamily.frozenHeatEquiv (A : BoundedChartFamily g) :
    M.Carrier → ComplexVector n ≃L[ℝ] ComplexVector n :=
  Classical.choose A.exists_frozen_heat_equivalences

theorem BoundedChartFamily.frozenHeatEquiv_norm_bounds (A : BoundedChartFamily g) (p : M.Carrier) :
    ‖(A.frozenHeatEquiv p : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤
        Real.sqrt A.frozenEllipticUpper ∧
      ‖((A.frozenHeatEquiv p).symm : ComplexVector n →L[ℝ] ComplexVector n)‖ ≤
        (Real.sqrt A.frozenEllipticLower)⁻¹ :=
  (Classical.choose_spec A.exists_frozen_heat_equivalences).1 p

theorem BoundedChartFamily.frozenHeatEquiv_gram (A : BoundedChartFamily g)
    (p : M.Carrier) (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    (∑ k : RIdx n, H (A.frozenHeatEquiv p (realVec k)) (A.frozenHeatEquiv p (realVec k))) =
      ∑ i : RIdx n, ∑ j : RIdx n,
        scalarSymbol (pullbackMatrix g (A.chart p) 0) i j * H (realVec i) (realVec j) :=
  (Classical.choose_spec A.exists_frozen_heat_equivalences).2 p H

def BoundedChartFamily.frozenHeatNormBudget (A : BoundedChartFamily g) (α : ℝ) : ℝ :=
  (1 + (Real.sqrt A.frozenEllipticUpper) ^ α) *
    (1 + (Real.sqrt A.frozenEllipticLower)⁻¹) ^ 2 *
    (1 + ((Real.sqrt A.frozenEllipticLower)⁻¹) ^ α)

theorem BoundedChartFamily.frozenHeatNormBudget_pos (A : BoundedChartFamily g) (α : ℝ) :
    0 < A.frozenHeatNormBudget α := by
  have := A.frozenEllipticLower_pos
  dsimp [BoundedChartFamily.frozenHeatNormBudget]
  positivity

theorem BoundedChartFamily.frozenHeatNormFactor_le
    (A : BoundedChartFamily g) {α : ℝ} (hα : 0 ≤ α) (p : M.Carrier) :
    L16Aux.constantHeatNormFactor α (A.frozenHeatEquiv p) ≤ A.frozenHeatNormBudget α :=
  L16Aux.constantHeatNormFactor_le hα (A.frozenHeatEquiv p)
    (A.frozenHeatEquiv_norm_bounds p).1 (A.frozenHeatEquiv_norm_bounds p).2

def BoundedChartFamily.frozenHeatDuhamel (A : BoundedChartFamily g) (p : M.Carrier)
    (f : Point n → ℝ) : Point n → ℝ := L16Aux.constantHeatDuhamel (A.frozenHeatEquiv p) f

theorem BoundedChartFamily.frozenHeatDuhamel_initial
    (A : BoundedChartFamily g) (p : M.Carrier) (f : Point n → ℝ) (x : Space n) :
    A.frozenHeatDuhamel p f (x, 0) = 0 :=
  L16Aux.constantHeatDuhamel_initial (A.frozenHeatEquiv p) f x

theorem BoundedChartFamily.frozenHeatDuhamel_smul
    (A : BoundedChartFamily g) (p : M.Carrier) (c : ℝ) (f : Point n → ℝ) (q : Point n) :
    A.frozenHeatDuhamel p (c • f) q = c * A.frozenHeatDuhamel p f q :=
  L16Aux.constantHeatDuhamel_smul (A.frozenHeatEquiv p) c f q

theorem BoundedChartFamily.frozenHeatDuhamel_add
    (A : BoundedChartFamily g) (p : M.Carrier) {F G : ℝ} {f h : Point n → ℝ}
    (hf : Continuous f) (hh : Continuous h) (hF : ∀ q, |f q| ≤ F) (hG : ∀ q, |h q| ≤ G)
    (q : Point n) (ht : 0 ≤ q.2) :
    A.frozenHeatDuhamel p (f + h) q = A.frozenHeatDuhamel p f q + A.frozenHeatDuhamel p h q :=
  L16Aux.constantHeatDuhamel_add_of_bounded (A.frozenHeatEquiv p) hf hh hF hG q ht

theorem BoundedChartFamily.frozenHeatDuhamel_equation
    (A : BoundedChartFamily g) (p : M.Carrier) {α T F : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    {f : Point n → ℝ} (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    {q : Point n} (hq : q ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T)
      (fun _ => scalarSymbol (pullbackMatrix g (A.chart p) 0)) (fun _ _ => 0)
      (A.frozenHeatDuhamel p f) q = f q :=
  L16Aux.constantHeatDuhamel_linearOp (A.frozenHeatEquiv p)
    (A.frozenHeatEquiv_gram p) hα hα1 hT hT1 hf hq

theorem BoundedChartFamily.frozenHeatDuhamel_controlled_bounds
    (A : BoundedChartFamily g) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : M.Carrier) (T F : ℝ), 0 < T → T ≤ 1 →
      ∀ f : Point n → ℝ, HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (A.frozenHeatDuhamel p f) (K * F) ∧
      (∀ q ∈ cylinder Set.univ 0 T,
        ‖spatialDD (A.frozenHeatDuhamel p f) q‖ ≤ K * F * T ^ (α / 2)) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun q => (A.frozenHeatDuhamel p f q, spatialD (A.frozenHeatDuhamel p f) q))
        (K * F * (T ^ (1 / 2 : ℝ) + T ^ ((1 - α) / 2))) := by
  obtain ⟨C, hC, hbound⟩ := L16Aux.constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨C * A.frozenHeatNormBudget α,
    mul_pos hC (A.frozenHeatNormBudget_pos α), ?_⟩
  intro p T F hT hT1 f hf
  have h := hbound (A.frozenHeatNormBudget α) (A.frozenHeatEquiv p)
    (A.frozenHeatNormFactor_le hα.le p) T F hT hT1 f hf
  simpa only [BoundedChartFamily.frozenHeatDuhamel, mul_assoc, mul_left_comm, mul_comm] using h

end Yau.LeafProofs.L17Aux
