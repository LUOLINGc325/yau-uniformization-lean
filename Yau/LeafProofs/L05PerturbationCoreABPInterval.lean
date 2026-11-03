import Yau.LeafProofs.L05PucciHarnackCylinder

noncomputable section

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perturb_core_abp_slope_subset {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    slopeSet n (q*ell) (q*L) ⊆ slopeSet n ell (2*L) := by
  intro A hA
  have hLower : (((q-1)*ell) • (1 : Mat n)).PosSemidef := Matrix.PosSemidef.one.smul (mul_nonneg (sub_nonneg.mpr hq1) hell)
  have hUpper : (((2-q)*L) • (1 : Mat n)).PosSemidef := Matrix.PosSemidef.one.smul (mul_nonneg (sub_nonneg.mpr hq2) (hell.trans hL))
  constructor
  · convert! hA.1.add hLower using 1
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  · convert! hA.2.add hUpper using 1
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring

theorem perturb_core_abp_pucci_le {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (H : Sym n) :
    pucciPlus (q*ell) (q*L) H ≤ pucciPlus ell (2*L) H := by
  apply pucciPlus_le (mul_le_mul_of_nonneg_left hL (zero_le_one.trans hq1))
  intro A hA
  exact tracePair_le_pucciPlus hell (perturb_core_abp_slope_subset hell hL hq1 hq2 hA) H

theorem perturb_core_abp_viscosity_widen {n : ℕ} {ell L q : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {Q : Set (Point n)} {v f : Point n → ℝ}
    (hv : viscositySub Q (fun H _ => pucciPlus (q*ell) (q*L) H) f v) :
    viscositySub Q (fun H _ => pucciPlus ell (2*L) H) f v := by
  intro p hp phi hphi ht
  have hh := hv p hp phi hphi ht
  have hP := perturb_core_abp_pucci_le hell hL hq1 hq2 (hessian phi p)
  change timeD Set.univ phi p-pucciPlus ell (2*L) (hessian phi p) ≤ f p
  linarith only [hh,hP]

end Yau.LeafProofs.L05Aux
