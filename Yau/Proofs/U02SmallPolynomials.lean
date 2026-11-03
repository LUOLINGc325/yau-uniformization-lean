import Yau.Proofs.U02PolynomialBounds
import Yau.Proofs.U02Subexponential

/-! Uniform small-orbit estimates for the actual `H_k` in an original model. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem polynomial_fixesZero_norm_le {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) : ‖P.eval z‖ ≤ P.coeffNorm * ‖z‖ := by
  have hvanish : ∀ i (m : Fin n →₀ ℕ), (m.sum fun _ e => e) < 1 → (P i).coeff m = 0 := by
    intro i m hm
    have hm0 : m = 0 := by
      by_contra hne
      have hp : 0 < m.sum (fun _ e => e) :=
        Finsupp.sum_pos (fun j hj => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)) hne
      omega
    subst m
    exact hP i
  simpa using polynomial_norm_le (q := 1) P hvanish hz

/-- The estimate is uniform over the entire exponential ball for every late
index. Its thresholds may depend on the supplied original model. -/
theorem model_H_small_ball {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {ρ : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv)
    {a b : ℝ} (ha : 0 < a) (hab : b < a) :
    ∀ᶠ k in atTop, ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-a * ρ o (tk k)) →
      ‖(H k).eval z‖ ≤ Real.exp (-b * ρ o (tk k)) := by
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  have hs := hp.2.1
  have hbound := subexponential_times_decay hs heta 1 a b hab
  filter_upwards [hbound, (tendsto_atTop.1 hs) 0] with k hk hsk
  intro z hz
  have hexp : Real.exp (-a * ρ o (tk k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  calc
    ‖(H k).eval z‖ ≤ (H k).coeffNorm * ‖z‖ :=
      polynomial_fixesZero_norm_le (H k) (hp.2.2.2.2.1 k).1 (hz.trans hexp)
    _ ≤ Real.exp (eta k * ρ o (tk k)) * Real.exp (-a * ρ o (tk k)) :=
      mul_le_mul (hcoeff k).1 hz (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-b * ρ o (tk k)) := by simpa only [one_mul] using hk

end Yau.NodeProofs.U02Proof
