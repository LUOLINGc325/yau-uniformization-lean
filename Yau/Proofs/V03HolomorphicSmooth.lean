import Yau.Proofs.V03HolomorphicDifferential

/-! Finite-dimensional holomorphic maps are complex smooth. This is proved
from native directional Cauchy calculus, including the zero-dimensional case. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem complex_holomorphic_contDiffOn_nat (m : ℕ)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ m f U := by
  induction m generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ m ih =>
    have hd : ContDiffOn ℂ m (fderiv ℂ f) U :=
      contDiffOn_clm_apply.mpr fun v =>
        ih (complex_holomorphic_fderiv_apply_differentiableOn hU hf v)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (contDiffOn_succ_iff_fderiv_of_isOpen (n := (m : ℕ∞ω)) hU).mpr
        ⟨hf, by simp, hd⟩

theorem complex_holomorphic_contDiffOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.mpr fun m => complex_holomorphic_contDiffOn_nat m hU hf

theorem cotangentHolomorphic_chart_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G) (x : M.Carrier) :
    ContDiffOn ℂ ∞ (fun z => G (cotangentChartInv x z)) (cotangentTarget x) :=
  complex_holomorphic_contDiffOn
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ) (hG x)

end Yau.Blueprint.V03Proof
