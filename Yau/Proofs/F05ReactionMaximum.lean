import Yau.Proofs.F05MaximumContact
import Yau.Proofs.F05TimeMultiplication

/-! The compact manifold maximum argument handles an actual bounded
zeroth-order reaction at positive contacts. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_manifold_reaction_maximum {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T lam upper : ℝ} (hT : 0 < T) (u : M.Carrier → ℝ → ℝ) (K : ℝ)
    (hCont : ContinuousOn (fun p : M.Carrier × ℝ => u p.1 p.2) (closure O ×ˢ Icc 0 T))
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i u))
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (hInit : ∀ x ∈ closure O, u x 0 ≤ 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u x t ≤ 0)
    (hOp : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, 0 < u x t → F05IntrinsicLinearOperator c h T u x t ≤ K*u x t) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, u x t ≤ 0 := by
  intro x hx t ht
  by_contra hn
  have hPos : 0 < u x t := lt_of_not_ge hn
  let θ := fun s : ℝ => Real.exp (-(K+1)*s)
  let v := fun x t => θ t*u x t
  have hθ : ContDiff ℝ 1 θ := by dsimp only [θ]; fun_prop
  have hθPos (s : ℝ) : 0 < θ s := Real.exp_pos _
  have hVCont : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (closure O ×ˢ Icc 0 T) :=
    (hθ.continuous.comp continuous_snd).continuousOn.mul hCont
  have hVC2 (i : Fin A.count) : C2 (F05Q A i T) (pull A i v) := F05_c2_time_mul hT (hC2 i) hθ
  have hVInit (y : M.Carrier) (hy : y ∈ closure O) : v y 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hθPos 0).le (hInit y hy)
  have hVBoundary (y : M.Carrier) (hy : y ∈ frontier O) (s : ℝ) (hs : s ∈ Icc 0 T) : v y s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hθPos s).le (hBoundary y hy s hs)
  obtain ⟨y,hy,s,hs,hVPos,hVOp⟩ := F05_positive_maximum_contact hA h c v hVCont hVC2 hEll
    hVInit hVBoundary ⟨x,hx,t,ht,mul_pos (hθPos t) hPos⟩
  have hUPos : 0 < u y s := by
    change 0 < θ s*u y s at hVPos
    exact (mul_pos_iff_of_pos_left (hθPos s)).mp hVPos
  have hDeriv : deriv θ s = -(K+1)*θ s := by
    simpa only [θ,id_eq,mul_one,one_mul,mul_comm] using (((hasDerivAt_id s).const_mul (-(K+1))).exp).deriv
  have hProduct := F05_intrinsic_time_mul hA h c hT u hC2 hθ (subset_closure hy) ⟨hs.1.le,hs.2⟩
  change F05IntrinsicLinearOperator c h T (fun x t => θ t*u x t) y s ≥ 0 at hVOp
  rw [hProduct,hDeriv] at hVOp
  have hMultiply := mul_le_mul_of_nonneg_left (hOp y hy s hs hUPos) (hθPos s).le
  change 0 < θ s*u y s at hVPos
  nlinarith

end Yau.Proofs.F05Aux
