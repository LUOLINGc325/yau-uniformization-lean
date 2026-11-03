import Yau.Proofs.C01CurvatureContraction

/-! The actual spatial-line curvature matrix has exactly the original
bisectional contraction in the central chart. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem spatial_line_curvature_eq_bisectional (g : HermitianField X.manifold)
    (x : Pt X) (ξ η : ComplexVector n)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun z => hMat g x z a b) (chartPt x x)) :
    let H : ℂ → Herm n := fun ζ => hMat g x (chartPt x x + ζ • η)
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1;
    (star (WithLp.ofLp ξ) ⬝ᵥ
      ((-H₁₂ + H₂ * (H 0)⁻¹ * H₁) *ᵥ WithLp.ofLp ξ)).re =
        bisectionalForm g x ξ η := by
  dsimp only
  let H : ℂ → Herm n := fun ζ => hMat g x (chartPt x x + ζ • η)
  let A : Fin n → Herm n := fun k => Matrix.of fun a b =>
    wirt (fun z => hMat g x z a b) (chartPt x x) (stdVec k)
  let B : Fin n → Herm n := fun l => Matrix.of fun a b =>
    wirtBar (fun z => hMat g x z a b) (chartPt x x) (stdVec l)
  let D : Fin n → Fin n → Herm n := fun k l => Matrix.of fun a b =>
    wirt (fun z => wirtBar (fun u => hMat g x u a b) z (stdVec l))
      (chartPt x x) (stdVec k)
  have hzero : H 0 = gMat g x := by simp only [H, zero_smul, add_zero, gMat]
  have hfirst : (Matrix.of fun i j => wirt (fun p => H p i j) 0 1) =
      (∑ k, η k • A k) := by
    ext a b
    change wirt (fun p => hMat g x (chartPt x x + p • η) a b) 0 1 = _
    rw [(spatial_affine_wirtinger _ _ _ (hg a b)).1, wirt_stdVec_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hbar : (Matrix.of fun i j => wirtBar (fun p => H p i j) 0 1) =
      (∑ l, star (η l) • B l) := by
    ext a b
    change wirtBar (fun p => hMat g x (chartPt x x + p • η) a b) 0 1 = _
    rw [(spatial_affine_wirtinger _ _ _ (hg a b)).2, wirtBar_stdVec_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hmixed : (Matrix.of fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1) =
      (∑ k, ∑ l, (η k * star (η l)) • D k l) := by
    ext a b
    change wirt (fun p => wirtBar
      (fun q => hMat g x (chartPt x x + q • η) a b) p 1) 0 1 = _
    rw [spatial_affine_mixed _ _ _ (hg a b),
      complex_mixedLevi_stdVec_sum _ _ _ (hg a b)]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  change (star (WithLp.ofLp ξ) ⬝ᵥ
    ((-(Matrix.of fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1) +
      (Matrix.of fun i j => wirtBar (fun p => H p i j) 0 1) * (H 0)⁻¹ *
        (Matrix.of fun i j => wirt (fun p => H p i j) 0 1)) *ᵥ WithLp.ofLp ξ)).re = _
  rw [hfirst, hbar, hmixed, hzero, curvature_direction_contraction]
  rfl

end Yau.NodeProofs.C01Aux
