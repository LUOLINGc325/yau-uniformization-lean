import Yau.LeafProofs.L05ViscosityPrimitives

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The exact derived coarse endpoint of perturbation Card P. This definition
records the endpoint to be proved and assumes no analytic provider. -/
def VariableConcaveCoarseSchauderGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ alpha beta ell L M fB uB : ℝ,
    0 < alpha → alpha < 1 → 0 < beta → beta < 1 → 0 < ell → ell ≤ L →
    0 ≤ M → 0 ≤ fB → 0 ≤ uB →
    ∃ eta C : ℝ, 0 < eta ∧ eta < min alpha beta ∧ 0 < C ∧
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
      ContinuousOn (fun z : Sym n × Point n => Phi z.1 z.2)
        (Set.univ ×ˢ backward 1) →
      (∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L) →
      (∀ p∈backward 1, ConcaveOn ℝ Set.univ (fun H => Phi H p)) →
      (∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
        |Phi H p-Phi H q| ≤ M*(1+‖H‖)*holderWeight beta p q) →
      |Phi 0 (0,0)| ≤ M → HolderBound alpha (backward 1) f fB →
      C2 (backward 1) u → (∀ p∈backward 1, |u p| ≤ uB) →
      (∀ p∈backward 1,
        timeD (backward 1) u p-Phi (hessian u p) p=f p) →
      SchauderBound eta (backward (3/4)) u C

end Yau.LeafProofs.L05Aux
