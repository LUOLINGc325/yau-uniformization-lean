import Yau.Proofs.Y03Inverse

/-! Continuity of the actual matrix operator norm and inverse in the coefficient topology. -/

open scoped Topology Matrix Matrix.Norms.Elementwise
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem continuous_matOpNorm : Continuous (fun A : Herm n => matOpNorm A) := by
  have h : Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous
  exact continuous_norm.comp h

theorem matrix_inverse_tendsto_of_isUnit {L : ℕ → Herm n} {A : Herm n}
    (hlim : Tendsto L atTop (𝓝 A)) (hA : IsUnit A) :
    Tendsto (fun H => (L H)⁻¹) atTop (𝓝 A⁻¹) := by
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  have hi : ContinuousAt (fun B : Herm n => B⁻¹) A := continuousAt_matrix_inv A (by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet : ContinuousAt (fun z : ℂ => z⁻¹) A.det))
  exact hi.tendsto.comp hlim

theorem strict_weight_eventual_limit {L : ℕ → Herm n} {A : Herm n} (w : Fin n → ℝ)
    (hlim : Tendsto L atTop (𝓝 A)) (hdiag : ∀ᶠ H in atTop, ∀ i, L H i i = 1)
    (hsupport : ∀ᶠ H in atTop, ∀ i j, i ≠ j → L H i j ≠ 0 → w i < w j) :
    (∀ i, A i i = 1) ∧ (∀ i j, i ≠ j → A i j ≠ 0 → w i < w j) := by
  have hcoord : ∀ i j, Tendsto (fun H => L H i j) atTop (𝓝 (A i j)) :=
    fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) j
  constructor
  · intro i
    have heq : (fun H => L H i i) =ᶠ[atTop] fun _ => (1 : ℂ) := hdiag.mono fun H hH => hH i
    exact tendsto_nhds_unique (hcoord i i) (tendsto_const_nhds.congr' heq.symm)
  · intro i j hij hne
    by_contra hn
    have heq : (fun H => L H i j) =ᶠ[atTop] fun _ => (0 : ℂ) := by
      filter_upwards [hsupport] with H hH
      by_contra hHzero
      exact hn (hH i j hij hHzero)
    exact hne (tendsto_nhds_unique (hcoord i j) (tendsto_const_nhds.congr' heq.symm))

end Yau.Blueprint.Alignment.Y03Proof
