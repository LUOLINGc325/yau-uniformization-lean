import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.LeafProofs.L16TemporalCutoff

/-! Time multiplication on the original physical cylinders keeps their
actual one-sided time derivative; no all-space spatial extension is assumed. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_timeD_time_mul {D : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {u : Point n → ℝ} (hu : C2 (cylinder D 0 T) u) {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    {p : Point n} (hp : p ∈ cylinder D 0 T) :
    timeD (cylinder D 0 T) (fun q => θ q.2*u q) p =
      deriv θ p.2*u p+θ p.2*timeD (cylinder D 0 T) u p := by
  have hFiber : {r | (p.1,r) ∈ cylinder D 0 T} = Icc 0 T := by ext r; exact and_iff_right hp.1
  have hU : HasDerivWithinAt (fun t => u (p.1,t))
      (timeD (cylinder D 0 T) u p) (Icc 0 T) p.2 := by
    simpa only [timeD,hFiber] using (hu.2.2.2.2.2 p hp).hasDerivWithinAt
  have hProd := ((hθ p.2).hasDerivAt.hasDerivWithinAt.mul hU).derivWithin
    (uniqueDiffOn_Icc hT p.2 hp.2)
  have hFun : θ*(fun t => u (p.1,t)) = fun t => θ t*u (p.1,t) := rfl
  rw [hFun] at hProd
  simpa only [timeD,hFiber,Prod.eta] using hProd

theorem F05_c2_time_mul {D : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {u : Point n → ℝ} (hu : C2 (cylinder D 0 T) u) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) :
    C2 (cylinder D 0 T) (fun p => θ p.2*u p) := by
  have hθc : Continuous (fun p : Point n => θ p.2) := hθ.continuous.comp continuous_snd
  have hθd : Continuous (fun p : Point n => deriv θ p.2) := hθ.continuous_deriv_one.comp continuous_snd
  have hDiff := hθ.differentiable (by norm_num)
  refine ⟨hθc.continuousOn.mul hu.1,?_,?_,?_,?_,?_⟩
  · exact (hθc.continuousOn.smul hu.2.1).congr (fun p hp => spatialD_time_mul hu θ hp)
  · exact (hθc.continuousOn.smul hu.2.2.1).congr (fun p hp => spatialDD_time_mul hu θ hp)
  · exact ((hθd.continuousOn.mul hu.1).add (hθc.continuousOn.mul hu.2.2.2.1)).congr
      (fun p hp => F05_timeD_time_mul hT hu hDiff hp)
  · intro p hp
    exact (hu.2.2.2.2.1 p hp).const_smul (θ p.2)
  · intro p hp
    exact (hDiff p.2).differentiableWithinAt.mul (hu.2.2.2.2.2 p hp)

theorem F05_intrinsic_time_mul {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (u : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, C2 (F05Q A i T) (pull A i u)) {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (fun x t => θ t*u x t) x t =
      θ t*F05IntrinsicLinearOperator c h T u x t+deriv θ t*u x t := by
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  rw [← heq]
  have hp : (z,t) ∈ F05Q A i T := ⟨hz,ht⟩
  have hProd := F05_c2_time_mul hT (hu i) hθ
  have hProdEq := F05_intrinsic_operator_eq_chart hA h c T (fun x t => θ t*u x t) i
    (p := (z,t)) hz (hProd.2.2.2.2.1 (z,t) hp)
  have hOldEq := F05_intrinsic_operator_eq_chart hA h c T u i
    (p := (z,t)) hz ((hu i).2.2.2.2.1 (z,t) hp)
  rw [hProdEq,hOldEq]
  have hPull : pull A i (fun x t => θ t*u x t) = (fun q => θ q.2*pull A i u q) := rfl
  rw [hPull]
  have hTimeEq : timeD (F05Q A i T) (fun q => θ q.2*pull A i u q) (z,t) =
      deriv θ t*pull A i u (z,t)+θ t*timeD (F05Q A i T) (pull A i u) (z,t) :=
    F05_timeD_time_mul hT (hu i) (hθ.differentiable (by norm_num)) hp
  have hD := spatialD_time_mul (hu i) θ hp
  have hDD := spatialDD_time_mul (hu i) θ hp
  unfold linearOp
  rw [hTimeEq,hD,hDD]
  simp only [smul_apply,smul_eq_mul]
  ring_nf
  simp only [mul_assoc,← Finset.mul_sum,pull]

end Yau.Proofs.F05Aux
