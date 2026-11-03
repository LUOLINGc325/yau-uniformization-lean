import Yau.Proofs.C01SpatialBisectional

/-! The original Ricci quadratic form is the actual metric trace of
the spatial-line curvature matrix, including at time zero. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem ricci_quadratic_eq_spatial_line_trace
    (g : HermitianField X.manifold) (x : Pt X) (η : ComplexVector n)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun z => hMat g x z a b) (chartTarget x)) :
    let H : ℂ → Herm n := fun ζ => hMat g x (chartPt x x + ζ • η)
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1;
    star (WithLp.ofLp η) ⬝ᵥ (ricci g x *ᵥ WithLp.ofLp η) =
      Matrix.trace ((H 0)⁻¹ * (-H₁₂ + H₂ * (H 0)⁻¹ * H₁)) := by
  dsimp only
  let z := chartPt x x
  let φ : ComplexVector n → ℝ := fun p => -logDet g x p
  let H : ℂ → Herm n := fun ζ => hMat g x (z + ζ • η)
  let S : Set ℂ := {ζ | z + ζ • η ∈ chartTarget x}
  have hz : z ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  have hchart : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hlog : ContDiffAt ℝ 2 (logDet g x) z := by
    have hdet := Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_det hg
    have hnz (p : ComplexVector n) (hp : p ∈ chartTarget x) :
        (hMat g x p).det.re ≠ 0 :=
      (Complex.pos_iff.mp (hMat_posDef g x p hp).det_pos).1.ne'
    exact (((Complex.reCLM.contDiff.comp_contDiffOn hdet).log hnz).contDiffAt
      (hchart.mem_nhds hz)).of_le (by simp)
  have hφ : ContDiffAt ℝ 2 φ z := hlog.neg
  have hsum : (∑ i, η i • stdVec i) = η := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have hp := levi_quadratic_eq_matrix hφ stdVec (WithLp.ofLp η)
  rw [hsum] at hp
  have hL : leviC φ z = ricci g x := by
    ext i j
    change wirt (fun p => wirtBar (fun q => ((-logDet g x q : ℝ) : ℂ)) p
      (stdVec i)) z (stdVec j) =
      -(wirt (fun p => wirtBar (fun q => (logDet g x q : ℂ)) p
        (stdVec i)) z (stdVec j))
    simp only [Complex.ofReal_neg]
    exact mixedLevi_neg_fn _ _ _ _
  change wirt (fun p => wirtBar (fun q => (φ q : ℂ)) p η) z η =
    star (WithLp.ofLp η) ⬝ᵥ (leviC φ z *ᵥ WithLp.ofLp η) at hp
  rw [hL] at hp
  have hfc : ContDiffAt ℝ 2 (fun p => (logDet g x p : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hlog
  have haff := spatial_affine_mixed (fun p => (logDet g x p : ℂ)) z η hfc
  have hS : IsOpen S := hchart.preimage (by fun_prop)
  have hzero : (0 : ℂ) ∈ S := by simpa only [S, Set.mem_setOf_eq, zero_smul, add_zero] using hz
  have hH (a b : Fin n) : ContDiffOn ℝ ∞ (fun ζ => H ζ a b) S :=
    (hg a b).comp (show ContDiffOn ℝ ∞ (fun ζ : ℂ => z + ζ • η) S from
      (show ContDiff ℝ ∞ (fun ζ : ℂ => z + ζ • η) from by fun_prop).contDiffOn)
      (fun ζ hζ => hζ)
  have hpos (ζ : ℂ) (hζ : ζ ∈ S) : (H ζ).PosDef := hMat_posDef g x _ hζ
  have ht := matrix_logDet_mixed_trace H S hS hH hpos 0 1 1 hzero
  calc
    _ = wirt (fun p => wirtBar (fun q => (φ q : ℂ)) p η) z η := hp.symm
    _ = -(wirt (fun p => wirtBar (fun q => (logDet g x q : ℂ)) p η) z η) := by
      simp only [φ, Complex.ofReal_neg]
      exact mixedLevi_neg_fn _ _ _ _
    _ = -(wirt (fun p => wirtBar
        (fun q : ℂ => (Real.log (H q).det.re : ℂ)) p 1) 0 1) := by
      exact congrArg Neg.neg haff.symm
    _ = _ := ht

end Yau.NodeProofs.C01Aux
