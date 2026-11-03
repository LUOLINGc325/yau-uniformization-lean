import Yau.Proofs.C01ClockTimeJets

/-! The pure spatial block is precisely the original central-chart
Ricci quadratic form, by the definitions of Ricci and the Levi matrix. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

theorem product_spatial_mixedLevi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} (z d : E) (w : ℂ) (hF : ContDiffAt ℝ 2 F (z, w)) :
    wirt (fun p => wirtBar F p (d, 0)) (z, w) (d, 0) =
      wirt (fun p => wirtBar (fun q => F (q, w)) p d) z d := by
  let γ : E → E × ℂ := fun p => (p, w)
  have hγ : ContDiffAt ℂ 2 γ z := contDiffAt_id.prodMk contDiffAt_const
  have hγd : HasFDerivAt γ ((ContinuousLinearMap.id ℂ E).prod 0) z := by
    simpa only [id_eq] using! (hasFDerivAt_id z).prodMk (hasFDerivAt_const w z)
  have hc := levi_direction_comp_holomorphic (f := F) (γ := γ) (z := z) hF hγ d
  rw [hγd.fderiv] at hc
  simpa only [γ, Function.comp_def, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hc.symm

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem negativeLogDetClock_mixed_spatial
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (d : ComplexVector n) (w : ℂ) :
    let t := Real.exp (2 * w.re)
    wirt (fun p => wirtBar (fun q : ComplexVector n × ℂ =>
      (negativeLogDetClock h x q : ℂ)) p (d, 0)) (chartPt x x, w) (d, 0) =
      star (WithLp.ofLp d) ⬝ᵥ (ricci (h t) x *ᵥ WithLp.ofLp d) := by
  dsimp only
  let t := Real.exp (2 * w.re)
  let z := chartPt x x
  let φ : ComplexVector n → ℝ := fun p => -logDet (h t) x p
  have hwhole : ContDiffAt ℝ 2 (negativeLogDetClock h x) (z, w) :=
    (negativeLogDetClock_contDiffAt hflow x (z, w)
      (mem_extChartAt_target (I := ComplexModel n) x)).of_le (by simp)
  have hφ₀ := ContDiffAt.comp (f := fun p : ComplexVector n => (p, w))
    (g := negativeLogDetClock h x) z hwhole (contDiffAt_id.prodMk contDiffAt_const)
  have hφ : ContDiffAt ℝ 2 φ z := hφ₀
  have hfc : ContDiffAt ℝ 2
      (fun q : ComplexVector n × ℂ => (negativeLogDetClock h x q : ℂ)) (z, w) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hwhole
  rw [product_spatial_mixedLevi z d w hfc]
  have hsum : (∑ i, d i • stdVec i) = d := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have hp := levi_quadratic_eq_matrix hφ stdVec (WithLp.ofLp d)
  rw [hsum] at hp
  have hL : leviC φ z = ricci (h t) x := by
    ext i j
    change wirt (fun p => wirtBar (fun q => ((-logDet (h t) x q : ℝ) : ℂ)) p
        (stdVec i)) z (stdVec j) =
      -(wirt (fun p => wirtBar (fun q => (logDet (h t) x q : ℂ)) p
        (stdVec i)) z (stdVec j))
    simp only [Complex.ofReal_neg]
    exact mixedLevi_neg_fn _ _ _ _
  change wirt (fun p => wirtBar (fun q => (φ q : ℂ)) p d) z d = _
  change _ = star (WithLp.ofLp d) ⬝ᵥ (leviC φ z *ᵥ WithLp.ofLp d) at hp
  rw [hL] at hp
  exact hp

end Yau.NodeProofs.C01Aux
