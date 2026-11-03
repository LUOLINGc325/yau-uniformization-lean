import Yau.Proofs.F04FiniteCaloricAlgebra

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem subcaloric_compact_mass_pointwise {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T t R a : ℝ} (ht : t ∈ Ioo 0 T) (u : Pt X → ℝ) (z χ : STF X)
    (hcal : ∀ x, heatOp h (Icc 0 T) z x t ≤ 0)
    (hz : ∀ x, 0 ≤ z x t) (hχ : ∀ x, 0 ≤ χ x t)
    (hχt : ∀ x, deriv (χ x) t ≤ a * χ x t) (x : Pt X) :
    massCutoff u R x *
      ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
        scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ≤
      (χ x t * massCutoff u R x * laplacian (h t) (fun y => z y t) x) * density ρ x t +
        a * (massCutoff u R x * (z x t * χ x t * density ρ x t)) := by
  have hzd := hcal x
  rw [heatOp, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at hzd
  have hzeq : deriv (z x) t ≤ laplacian (h t) (fun y => z y t) x := sub_nonpos.mp hzd
  have hp := (massCutoff_range u R x).1
  have hd := (density_pos ρ x t).le
  have hR := (hloc.2.2.2.2.2.2.2.2.2.2.1 x t ht.1.le).2
  have htime := mul_le_mul_of_nonneg_left (hχt x)
    (mul_nonneg (mul_nonneg hp (hz x)) hd)
  have hcurv : 0 ≤ scalarCurvature (h t) x *
      (massCutoff u R x * (z x t * χ x t * density ρ x t)) := by
    exact mul_nonneg hR (mul_nonneg hp (mul_nonneg (mul_nonneg (hz x) (hχ x)) hd))
  have hcalweight := mul_le_mul_of_nonneg_right hzeq
    (mul_nonneg (mul_nonneg hp (hχ x)) hd)
  nlinarith only [htime, hcurv, hcalweight]


end Yau.F04Proof
