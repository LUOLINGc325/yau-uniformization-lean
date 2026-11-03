import Yau.Proofs.C01RicciCurvatureTrace
import Yau.Proofs.C01StrictTrace
import Yau.Proofs.C01DimensionPositive

/-! Strict bisectional curvature gives strict positivity of the original
Ricci quadratic form by the actual metric trace. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem griffithsPositive_ricci_quadratic_pos
    (g : HermitianField X.manifold) (hpositive : GriffithsPositive g)
    (hg : ∀ x a b, ContDiffOn ℝ ∞ (fun z => hMat g x z a b) (chartTarget x))
    (x : Pt X) (η : ComplexVector n) (hη : η ≠ 0) :
    0 < (star (WithLp.ofLp η) ⬝ᵥ (ricci g x *ᵥ WithLp.ofLp η)).re := by
  let H : ℂ → Herm n := fun ζ => hMat g x (chartPt x x + ζ • η)
  let H₁ : Herm n := Matrix.of fun i j => wirt (fun p => H p i j) 0 1
  let H₂ : Herm n := Matrix.of fun i j => wirtBar (fun p => H p i j) 0 1
  let H₁₂ : Herm n := Matrix.of fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1
  let C : Herm n := -H₁₂ + H₂ * (H 0)⁻¹ * H₁
  have htwo (a b : Fin n) :
      ContDiffAt ℝ 2 (fun z => hMat g x z a b) (chartPt x x) :=
    ((hg x a b).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target (I := ComplexModel n) x))).of_le (by simp)
  have hC (v : Fin n → ℂ) (hv : v ≠ 0) : 0 < (star v ⬝ᵥ (C *ᵥ v)).re := by
    let ξ : ComplexVector n := WithLp.toLp 2 v
    have hξ : ξ ≠ 0 := by
      intro hz
      apply hv
      exact congrArg WithLp.ofLp hz
    have hp := hpositive x ξ η hξ hη
    rw [← spatial_line_curvature_eq_bisectional g x ξ η htwo] at hp
    change 0 < (star (WithLp.ofLp ξ) ⬝ᵥ (C *ᵥ WithLp.ofLp ξ)).re at hp
    simpa only [ξ, WithLp.ofLp_toLp] using hp
  have hpos : ((H 0)⁻¹).PosDef := by
    apply Matrix.PosDef.inv
    simpa only [H, zero_smul, add_zero] using
      hMat_posDef g x (chartPt x x) (mem_extChartAt_target (I := ComplexModel n) x)
  have htrace := trace_mul_pos_of_real_quadratics (original_manifold_dimension_pos X.manifold)
    (H 0)⁻¹ C hpos hC
  rw [ricci_quadratic_eq_spatial_line_trace g x η (hg x)]
  exact htrace

end Yau.NodeProofs.C01Aux
