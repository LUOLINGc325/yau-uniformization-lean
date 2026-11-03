import Yau.Proofs.P04BufferedModels
import Yau.Proofs.P04SeriesJets

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff BigOperators

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- ONE sequence of positive coefficients is chosen after the actual
all-order compact budgets for BOTH norm and coefficient models exist. -/
theorem exists_canonical_coefficients_with_all_jets (g : SmoothMetric M)
    (S : ℕ → CanonicalSection M) (hS : ∀ i, IsHolomorphicCanonical (S i))
    (a : ℕ → M.Carrier) (β : ℕ → ComplexVector n → ℝ)
    (hβ : ∀ j, ContDiff ℝ ∞ (β j)) (hcβ : ∀ j, HasCompactSupport (β j))
    (hsβ : ∀ j, tsupport (β j) ⊆ chartTarget (a j)) (B : ℕ → ℝ) :
    ∃ c : ℕ → ℝ,
      (∀ i, 0 < c i ∧ c i*Real.exp (B i) ≤ (1/2 : ℝ)^i) ∧
      ∀ j,
        (ContDiff ℝ ∞ (fun z => ∑' i, c i*(β j z*inChart (a j) (canonicalNormSq g.form (S i)) z)) ∧
          ∀ q z, Tendsto (fun N => iteratedFDeriv ℝ q
            (fun w => ∑ i ∈ Finset.range N, c i*(β j w*inChart (a j) (canonicalNormSq g.form (S i)) w)) z)
            atTop (𝓝 (iteratedFDeriv ℝ q
              (fun w => ∑' i, c i*(β j w*inChart (a j) (canonicalNormSq g.form (S i)) w)) z))) ∧
        (ContDiff ℝ ∞ (fun z => ∑' i, c i*(β j z*‖canonicalCoeff (S i) (a j) z‖^2)) ∧
          ∀ q z, Tendsto (fun N => iteratedFDeriv ℝ q
            (fun w => ∑ i ∈ Finset.range N, c i*(β j w*‖canonicalCoeff (S i) (a j) w‖^2)) z)
            atTop (𝓝 (iteratedFDeriv ℝ q
              (fun w => ∑' i, c i*(β j w*‖canonicalCoeff (S i) (a j) w‖^2)) z))) := by
  let b : ℕ → ℕ → ComplexVector n → ℝ := fun i j z =>
    if (Nat.unpair j).2=0 then β (Nat.unpair j).1 z*
      inChart (a (Nat.unpair j).1) (canonicalNormSq g.form (S i)) z
    else β (Nat.unpair j).1 z*‖canonicalCoeff (S i) (a (Nat.unpair j).1) z‖^2
  have hb (i j : ℕ) : ContDiff ℝ ∞ (b i j) := by
    dsimp only [b]
    split_ifs
    · exact buffered_canonical_norm_smooth g (S i) (hS i) _ (hβ _) (hsβ _)
    · exact buffered_canonical_coefficient_smooth (S i) (hS i) _ (hβ _) (hsβ _)
  have hcompact (i j : ℕ) : HasCompactSupport (b i j) := by
    dsimp only [b]
    split_ifs <;> exact buffered_model_compact (hcβ _)
  obtain ⟨c,hc,hsum⟩ := exists_coefficients_with_smooth_sums_and_jets b hb hcompact B
  refine ⟨c,hc,fun j => ?_⟩
  constructor
  · simpa only [b,Nat.unpair_pair,ite_true] using hsum (Nat.pair j 0)
  · simpa only [b,Nat.unpair_pair,one_ne_zero,ite_false] using hsum (Nat.pair j 1)

end Yau.Proofs.P04Aux
