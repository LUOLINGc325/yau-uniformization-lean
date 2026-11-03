import Yau.Proofs.U02ModelSeparation

/-! Equality of the same corrected limit forces exponentially small
separation of the two actual raw coordinate orbits. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem models_raw_separation {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {a : ℝ} (ha : 0 < a) {u v : ℕ → ComplexVector n} {p q : ComplexVector n}
    (hu : ∀ᶠ k in atTop, ‖u k‖ ≤ Real.exp (-a * rho o (tk k)))
    (hv : ∀ᶠ k in atTop, ‖v k‖ ≤ Real.exp (-a * rho o (tk k)))
    (hpu : ∀ᶠ k in atTop,
      ‖(forwardComp G k).eval p - (H k).eval (u k)‖ ≤ Real.exp (-6 * rho o (tk k)))
    (hqv : ∀ᶠ k in atTop,
      ‖(forwardComp G k).eval q - (H k).eval (v k)‖ ≤ Real.exp (-6 * rho o (tk k)))
    (hpq : p = q) :
    ∀ᶠ k in atTop, ‖u k - v k‖ ≤ Real.exp (-5 * rho o (tk k)) := by
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  filter_upwards [hu, hv, hpu, hqv, models_H_lower_distance hp ha,
    models_H_inverse_linear_exp hp (by norm_num : (0 : ℝ) < 1 / 4),
    subexponential_times_decay hp.2.1 hconst 4 (23 / 4) 5 (by norm_num)]
    with k huk hvk hpuk hqvk hlower hlin hdecay
  have hdiff : ‖(H k).eval (u k) - (H k).eval (v k)‖ ≤
      2 * Real.exp (-6 * rho o (tk k)) := by
    have heq : (H k).eval (u k) - (H k).eval (v k) =
        -((forwardComp G k).eval p - (H k).eval (u k)) +
        ((forwardComp G k).eval q - (H k).eval (v k)) := by rw [hpq]; abel
    rw [heq]
    apply (norm_add_le _ _).trans
    simpa only [norm_neg, two_mul] using add_le_add hpuk hqvk
  calc
    ‖u k - v k‖ ≤ 2 * matOpNorm (H k).linearPart⁻¹ *
        ‖(H k).eval (u k) - (H k).eval (v k)‖ := hlower _ _ huk hvk
    _ ≤ 2 * Real.exp ((1 / 4) * rho o (tk k)) *
        (2 * Real.exp (-6 * rho o (tk k))) := by gcongr
    _ = 4 * Real.exp (-(23 / 4) * rho o (tk k)) := by
      rw [show 2 * Real.exp ((1 / 4) * rho o (tk k)) *
          (2 * Real.exp (-6 * rho o (tk k))) =
          4 * (Real.exp ((1 / 4) * rho o (tk k)) *
            Real.exp (-6 * rho o (tk k))) by ring, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-5 * rho o (tk k)) := by
      simpa only [zero_mul, Real.exp_zero, mul_one] using hdecay

end Yau.NodeProofs.U02Proof
