import Yau.Proofs.C01ScalarHarnack

/-! The zero spatial direction in the original scalar Harnack
inequality implies monotonicity of the same scalar-curvature clock tR. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_time_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv (fun s => scalarCurvature (h s) x) t + t⁻¹ * scalarCurvature (h t) x := by
  simpa using localizedFlow_scalar_harnack hflow hjoint x ht (0 : ComplexVector n)

theorem localizedFlow_scalar_clock_hasDerivAt_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => s * scalarCurvature (h s) x)
      (scalarCurvature (h t) x + t * deriv (fun s => scalarCurvature (h s) x) t) t ∧
    0 ≤ scalarCurvature (h t) x + t * deriv (fun s => scalarCurvature (h s) x) t := by
  constructor
  · simpa only [one_mul, id_eq] using!
      (hasDerivAt_id t).mul (localizedFlow_scalar_hasDerivAt hflow x ht)
  · have hp := mul_nonneg ht.le (localizedFlow_scalar_time_harnack hflow hjoint x ht)
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at hp
    linarith

theorem localizedFlow_scalar_clock_monotoneOn
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) :
    MonotoneOn (fun t => t * scalarCurvature (h t) x) (Set.Ioi 0) := by
  have hd (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :=
    localizedFlow_scalar_clock_hasDerivAt_nonneg hflow hjoint x ht
  have hInt : interior (Set.Ioi (0 : ℝ)) = Set.Ioi 0 := isOpen_Ioi.interior_eq
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hd t ht).1.continuousAt.continuousWithinAt
  · intro t ht
    rw [hInt] at ht
    exact (hd t ht).1.differentiableAt.differentiableWithinAt
  · intro t ht
    rw [hInt] at ht
    have h := hd t ht
    rw [h.1.deriv]
    exact h.2

end Yau.NodeProofs.C01Aux
