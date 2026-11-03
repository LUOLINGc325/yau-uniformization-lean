import Yau.LeafProofs.L16ClassicalCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem spatialD_time_mul {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (θ : ℝ → ℝ) {p : Point n} (hp : p ∈ Q) :
    spatialD (fun q => θ q.2*u q) p = θ p.2 • spatialD u p := by
  simpa only [spatialD] using
    fderiv_const_mul ((hu.2.2.2.2.1 p hp).differentiableAt (by norm_num)) (θ p.2)

theorem spatialDD_time_mul {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (θ : ℝ → ℝ) {p : Point n} (hp : p ∈ Q) :
    spatialDD (fun q => θ q.2*u q) p = θ p.2 • spatialDD u p := by
  have h := secondFDeriv_mul (contDiffAt_const (c := θ p.2)) (hu.2.2.2.2.1 p hp)
  simpa only [spatialDD,fderiv_fun_const,fderiv_zero,Pi.zero_apply,
    ContinuousLinearMap.zero_smulRight,ContinuousLinearMap.smulRight_zero,
    zero_smul,smul_zero,add_zero] using h

theorem timeD_time_mul {n : ℕ} {l r : ℝ} {u : Point n → ℝ}
    (hlr : l < r) (hu : C2 (cylinder Set.univ l r) u)
    {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ) {p : Point n}
    (hp : p ∈ cylinder Set.univ l r) :
    timeD (cylinder Set.univ l r) (fun q => θ q.2*u q) p =
      deriv θ p.2*u p+θ p.2*timeD (cylinder Set.univ l r) u p := by
  have hSlice : {t : ℝ | (p.1,t) ∈ cylinder (n := n) Set.univ l r} = Set.Icc l r := by
    ext t
    simp [Yau.Parabolic.cylinder]
  have huD : HasDerivWithinAt (fun t => u (p.1,t))
      (timeD (cylinder Set.univ l r) u p) (Set.Icc l r) p.2 := by
    simpa only [timeD,hSlice] using (hu.2.2.2.2.2 p hp).hasDerivWithinAt
  have hProd := ((hθ p.2).hasDerivAt.hasDerivWithinAt.mul huD).derivWithin
    (uniqueDiffOn_Icc hlr p.2 hp.2)
  have hMul : θ*(fun t => u (p.1,t)) = (fun t => θ t*u (p.1,t)) := by funext t; rfl
  rw [hMul] at hProd
  simpa only [timeD,hSlice,Prod.eta] using hProd

theorem c2_time_mul {n : ℕ} {l r : ℝ} {u : Point n → ℝ}
    (hlr : l < r) (hu : C2 (cylinder Set.univ l r) u)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) :
    C2 (cylinder Set.univ l r) (fun p => θ p.2*u p) := by
  have hθc : Continuous (fun p : Point n => θ p.2) := hθ.continuous.comp continuous_snd
  have hθd : Continuous (fun p : Point n => deriv θ p.2) :=
    hθ.continuous_deriv_one.comp continuous_snd
  have hD := hθ.differentiable (by norm_num)
  refine ⟨hθc.continuousOn.mul hu.1,?_,?_,?_,?_,?_⟩
  · exact (hθc.continuousOn.smul hu.2.1).congr
      (fun p hp => spatialD_time_mul hu θ hp)
  · exact (hθc.continuousOn.smul hu.2.2.1).congr
      (fun p hp => spatialDD_time_mul hu θ hp)
  · exact ((hθd.continuousOn.mul hu.1).add (hθc.continuousOn.mul hu.2.2.2.1)).congr
      (fun p hp => timeD_time_mul hlr hu hD hp)
  · intro p hp
    exact (hu.2.2.2.2.1 p hp).const_smul (θ p.2)
  · intro p hp
    exact ((hD p.2).differentiableWithinAt).mul (hu.2.2.2.2.2 p hp)

theorem linearOp_time_mul {n : ℕ} {l r : ℝ} {u : Point n → ℝ}
    (hlr : l < r) (hu : C2 (cylinder Set.univ l r) u)
    {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    linearOp (cylinder Set.univ l r) a b (fun q => θ q.2*u q) p =
      θ p.2*linearOp (cylinder Set.univ l r) a b u p+deriv θ p.2*u p := by
  have hPrincipal : (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      a p i j*(θ p.2*spatialDD u p (Yau.realVec i) (Yau.realVec j))) =
      θ p.2*(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        a p i j*spatialDD u p (Yau.realVec i) (Yau.realVec j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hDrift : (∑ i : Yau.RIdx n, b p i*(θ p.2*spatialD u p (Yau.realVec i))) =
      θ p.2*(∑ i : Yau.RIdx n, b p i*spatialD u p (Yau.realVec i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [linearOp,timeD_time_mul hlr hu hθ hp,spatialD_time_mul hu θ hp,
    spatialDD_time_mul hu θ hp,smul_apply,smul_eq_mul]
  rw [hPrincipal,hDrift]
  ring

end Yau.LeafProofs.L16Aux
