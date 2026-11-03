import Yau.Proofs.F04FlowMassDerivative

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem caloric_compact_mass_pointwise {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T t R a : ℝ} (ht : t ∈ Ioo 0 T) (u : Pt X → ℝ) (z χ : STF X)
    (hcal : ∀ x, heatOp h (Icc 0 T) z x t = 0)
    (hz : ∀ x, 0 ≤ z x t) (hχ : ∀ x, 0 ≤ χ x t)
    (hχt : ∀ x, deriv (χ x) t ≤ a * χ x t) (x : Pt X) :
    massCutoff u R x *
      ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
        scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ≤
      (χ x t * massCutoff u R x * laplacian (h t) (fun y => z y t) x) * density ρ x t +
        a * (massCutoff u R x * (z x t * χ x t * density ρ x t)) := by
  have hzd := hcal x
  rw [heatOp, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at hzd
  have hzeq : deriv (z x) t = laplacian (h t) (fun y => z y t) x := sub_eq_zero.mp hzd
  have hp := (massCutoff_range u R x).1
  have hd := (density_pos ρ x t).le
  have hR := (hloc.2.2.2.2.2.2.2.2.2.2.1 x t ht.1.le).2
  have htime := mul_le_mul_of_nonneg_left (hχt x)
    (mul_nonneg (mul_nonneg hp (hz x)) hd)
  have hcurv : 0 ≤ scalarCurvature (h t) x *
      (massCutoff u R x * (z x t * χ x t * density ρ x t)) := by
    exact mul_nonneg hR (mul_nonneg hp (mul_nonneg (mul_nonneg (hz x) (hχ x)) hd))
  rw [hzeq]
  nlinarith only [htime, hcurv]

theorem caloric_mass_coefficient_bound {n : ℕ} {C p I : ℝ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hI : 0 ≤ I) :
    ((n : ℝ) * C + C * (1 + p)) * I ≤ (((n : ℝ) + 1) * C) * (1 + p) * I := by
  have hh : 0 ≤ (n : ℝ) * C * p * I := by positivity
  nlinarith only [hh]

theorem dominated_caloric_initial_zero {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 ≤ T) {z : STF X}
    (hz : ∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t) : ∀ x, z x 0 = 0 := by
  intro x
  have hx := hz x 0 ⟨le_rfl, hT⟩
  rw [rho_initial o h U P ρ hloc x] at hx
  exact le_antisymm hx.2 hx.1

end Yau.F04Proof
