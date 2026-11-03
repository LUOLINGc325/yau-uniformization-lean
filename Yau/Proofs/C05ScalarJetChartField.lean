import Yau.Proofs.C05RicciSquareJetsGeneric

/-! Local equality with an actual fixed-chart scalar field identifies the
computed covariant jets used in the finite contraction budgets. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.Proofs.C05RicciSquareJetsAux
variable {n r : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem computedJet_congr_on (k : HermitianField M) (c : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (m : ℕ)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hAB : ∀ z ∈ O, A z = B z)
    {z : ComplexVector n} (hz : z ∈ O) :
    Generic.jet k c A m z = Generic.jet k c B m z := by
  induction m generalizing z with
  | zero => exact hAB z hz
  | succ m ih =>
      apply covariantD_eventuallyEq
      filter_upwards [hO.mem_nhds hz] with u hu
      exact ih hu

theorem computedScalarJet_norm_eq (k : HermitianField M) (c : M.Carrier)
    (f : M.Carrier → ℝ) (A : ComplexVector n → CovTensor n 0)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hA : ∀ z ∈ O, ∀ v : Fin 0 → RIdx n, A z v = inChart c f z)
    {z : ComplexVector n} (hz : z ∈ O) (m : ℕ) (hm : m ≤ 3)
    (G : Matrix (RIdx n) (RIdx n) ℝ) :
    metricTensorNorm G (Generic.jet k c A m z) = metricTensorNorm G (scalarJet k f c m z) := by
  have he (m : ℕ) : Generic.jet k c A m z =
      Generic.jet k c (fun u (_ : Fin 0 → RIdx n) => inChart c f u) m z := by
    apply computedJet_congr_on k c A _ m hO _ hz
    intro u hu
    funext v
    exact hA u hu v
  interval_cases m <;> exact congrArg (metricTensorNorm G) (he _)

theorem ricciPairWord_eval (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n 2) (v : Fin 0 → RIdx n) :
    ricciSquareWord.eval G⁻¹ A B v = covTensorPair G A B := by
  unfold Word2.eval covTensorPair
  rw [← (pairFunctionEquiv (RIdx n)).symm.sum_comp]
  simp only [Fintype.sum_prod_type,pairFunctionEquiv,ricciSquareWord,Equiv.coe_fn_symm_mk,
    Sum.elim_inr,Fin.cases_zero,Fin.cases_succ,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  rfl

end Yau.Proofs.C05Aux
