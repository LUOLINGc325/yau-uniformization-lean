import Yau.Proofs.E01Matrix
import Yau.LeafProofs.L22LeviBasic

/-! The genuine matrix Levi lower bound has the same scalar quadratic
normalization used in the planar-support construction. -/

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs.L22Aux Yau.NodeProofs.E01Aux

variable {n : ℕ}

theorem complexLeviQuadratic_ge_of_HermLE (f : ComplexVector n → ℝ)
    (z v : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) (H : Herm n) (κ : ℝ)
    (hlo : HermLE ((κ : ℂ) • H) (leviC f z)) :
    κ * ellipsoidQuadratic H v ≤ complexLeviQuadratic f z v := by
  have Hq := ellipsoidQuadratic_nonneg hlo v
  change 0 ≤ (star (WithLp.ofLp v) ⬝ᵥ
    ((leviC f z - (κ : ℂ) • H) *ᵥ WithLp.ofLp v)).re at Hq
  simp only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] at Hq
  rw [leviC_quadratic_re hf v] at Hq
  change ellipsoidQuadratic ((κ : ℂ) • H) v ≤ complexLeviQuadratic f z v at Hq
  rwa [ellipsoidQuadratic_real_smul] at Hq

end Yau.Proofs.C03Aux
