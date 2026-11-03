import Yau.Proofs.F01ALocalLeviLimit
import Yau.Proofs.F01PotentialMetricAssembly
import Yau.Proofs.F01MatrixLimitOrder

/-! The retained chart is used at the actual queried point. Its
invertible holomorphic coordinate differential recovers the native Levi
limit, and eventual actual metric orders pass to the same potential. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HermitianMatrixAssemblyAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem actual_native_levi_limit_of_local_chart_levi_limit
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (f : ℕ → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (hf : ∀ᶠ m in atTop, ContDiffAt ℝ 2 (inChart (e z) (f m)) (chartPt (e z) (e z)))
    (hu : ContDiffAt ℝ 2 (inChart (e z) u) (chartPt (e z) (e z)))
    (hChart : Tendsto (fun m => leviC (fun w => f m (e w)) z) atTop
      (𝓝 (leviC (fun w => u (e w)) z))) :
    Tendsto (fun m => levi (f m) (e z)) atTop (𝓝 (levi u (e z))) := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hDet : J.det ≠ 0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z)))
  have hInv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hDet)
  have hStar : (J⁻¹)ᴴ * Jᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hInv, Matrix.conjTranspose_one]
  have hRecover (q : M.Carrier → ℝ)
      (hq : ContDiffAt ℝ 2 (inChart (e z) q) (chartPt (e z) (e z))) :
      (J⁻¹)ᴴ * leviC (fun w => q (e w)) z * J⁻¹ = levi q (e z) := by
    rw [(local_holomorphic_chart_second_data q e he hz hq).2]
    change (J⁻¹)ᴴ * (Jᴴ * levi q (e z) * J) * J⁻¹ = _
    calc
      _ = ((J⁻¹)ᴴ * Jᴴ) * levi q (e z) * (J * J⁻¹) := by noncomm_ring
      _ = _ := by rw [hStar, hInv]; simp
  have hLimit : Tendsto (fun m => (J⁻¹)ᴴ * leviC (fun w => f m (e w)) z * J⁻¹) atTop
      (𝓝 ((J⁻¹)ᴴ * leviC (fun w => u (e w)) z * J⁻¹)) :=
    (tendsto_const_nhds.mul hChart).mul tendsto_const_nhds
  rw [hRecover u hu] at hLimit
  exact hLimit.congr' (hf.mono (fun m hm => hRecover (f m) hm))

theorem actual_native_potential_matrix_limit
    (g : HermitianField M) (f : ℕ → M.Carrier → ℝ → ℝ)
    (U : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ)
    (hLevi : Tendsto (fun m => levi (fun y => f m y t) x) atTop
      (𝓝 (levi (fun y => U y t) x))) :
    Tendsto (fun m => nativePotentialMatrix g (f m) t x) atTop
      (𝓝 (nativePotentialMatrix g U t x)) := by
  exact tendsto_const_nhds.add hLevi

theorem actual_rayleigh_upper_factor_tendsto_one
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (R : ℝ) :
    Tendsto (fun m => Real.exp (2 * R / L m)) atTop (𝓝 1) := by
  have hZero : Tendsto (fun m => 2 * R / L m) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hL) :
        Tendsto (fun m => (2 * R) * (L m)⁻¹) atTop (𝓝 ((2 * R) * 0)))
  simpa only [Real.exp_zero, Function.comp_def] using
    Real.continuous_exp.continuousAt.tendsto.comp hZero

theorem actual_native_potential_orders_of_matrix_limit
    (g : HermitianField M) (f : ℕ → M.Carrier → ℝ → ℝ)
    (U : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ)
    {ell : ℝ} (hell : 0 < ell) (c : ℕ → ℝ)
    (hMatrix : Tendsto (fun m => nativePotentialMatrix g (f m) t x) atTop
      (𝓝 (nativePotentialMatrix g U t x)))
    (hc : Tendsto c atTop (𝓝 1))
    (hLower : ∀ᶠ m in atTop,
      (nativePotentialMatrix g (f m) t x - (ell : ℂ) • gMat g x).PosSemidef)
    (hUpper : ∀ᶠ m in atTop,
      ((c m : ℂ) • gMat g x - nativePotentialMatrix g (f m) t x).PosSemidef) :
    (nativePotentialMatrix g U t x).PosDef ∧
      HermLE (nativePotentialMatrix g U t x) (gMat g x) := by
  have hEntry (i j : Fin n) :
      Tendsto (fun m => nativePotentialMatrix g (f m) t x i j) atTop
        (𝓝 (nativePotentialMatrix g U t x i j)) := by
    have hEval : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) := by fun_prop
    exact hEval.continuousAt.tendsto.comp hMatrix
  have hLo := matrix_lower_order_of_entry_limits (fun _ => gMat g x)
    (fun m => nativePotentialMatrix g (f m) t x) (gMat g x)
    (nativePotentialMatrix g U t x) ell (fun _ _ => tendsto_const_nhds) hEntry hLower
  have hHi := matrix_upper_order_of_entry_limits (fun _ => gMat g x)
    (fun m => nativePotentialMatrix g (f m) t x) c (gMat g x)
    (nativePotentialMatrix g U t x) 1 (fun _ _ => tendsto_const_nhds) hEntry hc hUpper
  refine ⟨matrix_posDef_of_positive_lower_order (canonical_gMat_posDef g x) hell hLo, ?_⟩
  simpa only [HermLE, Complex.ofReal_one, one_smul] using hHi

end Yau.NodeProofs.F01Aux
