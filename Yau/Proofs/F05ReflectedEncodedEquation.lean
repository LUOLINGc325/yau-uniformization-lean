import Yau.Proofs.F05NonlinearEquationTransfer
import Yau.Proofs.F05ReflectedZeroFamily
import Yau.Proofs.F05SmoothTimeTranslation

/-! The reconstructed fixed-cylinder field satisfies the original shifted
equation exactly before its moving endpoint. The four actual encoded jets
therefore supply the eventual equation required by the closed limit. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_reflected_zero_encoded_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p w : M.Carrier → ℝ → ℝ)
    {T s b r τ β : ℝ} (hδ : 0 < T-s) (hs : 0 ≤ s) (hb : 0 < b)
    (hsr : s < r) (hrτ : r < τ) (hτT : τ < T) (hbr : b/2 ≤ r-s)
    (hp : SmoothSpaceTime p (Icc 0 T))
    (hw : F05CompactDirichletSolution O A h p τ w)
    (hF : ∀ i, C2 (F05Q A i (T-s)) (pull A i (F05ReflectedZeroField s b τ p w)))
    (u : F05CompatibleJetGraph A β hδ.le)
    (hEval : ∀ i (z : F05Q A i (T-s)),
      (u.val i).val.1 z = pull A i (F05ReflectedZeroField s b τ p w) z.val ∧
      (u.val i).val.2.1 z = spatialD (pull A i (F05ReflectedZeroField s b τ p w)) z.val ∧
      (u.val i).val.2.2.1.val.1 z = spatialDD (pull A i (F05ReflectedZeroField s b τ p w)) z.val ∧
      (u.val i).val.2.2.2.val.1 z =
        timeD (F05Q A i (T-s)) (pull A i (F05ReflectedZeroField s b τ p w)) z.val) :
    ∀ i (z : F05Q A i (T-s)), z.val.2 ∈ Icc (r-s) (τ-s) →
      timeD (F05Q A i (T-s)) (pull A i (F05ManifoldTimeShift s p)) z.val+(u.val i).val.2.2.2.val.1 z =
        Real.exp (-(pull A i (F05ManifoldTimeShift s p) z.val+(u.val i).val.1 z))*
          ((∑ a,∑ c,flatA (h (z.val.2+s)) A i z.val a c*
              (spatialDD (pull A i (F05ManifoldTimeShift s p)) z.val+(u.val i).val.2.2.1.val.1 z)
                (realVec a) (realVec c))+
            ∑ a,flatB (h (z.val.2+s)) A i z.val a*
              (spatialD (pull A i (F05ManifoldTimeShift s p)) z.val+(u.val i).val.2.1 z) (realVec a))+
          (1-Real.exp (-(pull A i (F05ManifoldTimeShift s p) z.val+(u.val i).val.1 z)))*
            scalarCurvature (h (z.val.2+s)) (lift A i z.val.1) := by
  have hτs : s < τ := hsr.trans hrτ
  have hMapT : MapsTo (fun t : ℝ => t+s) (Icc 0 (T-s)) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hpShift := F05_smooth_spacetime_time_shift s hMapT p hp
  have hPC2 (i : Fin A.count) : C2 (F05Q A i (T-s)) (pull A i (F05ManifoldTimeShift s p)) :=
    F05_smooth_actual_chart_c2 hA hpShift hδ le_rfl i
  obtain ⟨γ,L,hγ,hγ1,hL,hW,hCont,h0,hBoundary,hEquation⟩ := hw
  let V := F05ManifoldTimeShift s w
  let F := F05ReflectedZeroField s b τ p w
  let U := fun x t => F05ManifoldTimeShift s p x t+F x t
  have hMapτ : MapsTo (fun t : ℝ => t+s) (Icc 0 (τ-s)) (Icc 0 τ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hMapOne : MapsTo (fun t : ℝ => 1*t+s) (Icc 0 (τ-s)) (Icc 0 τ) := by
    simpa only [one_mul] using hMapτ
  have hVC2 (i : Fin A.count) : C2 (F05Q A i (τ-s)) (pull A i V) := by
    rw [F05_manifold_time_shift_pull]
    exact F05_c2_timeAffine (sub_pos.mpr hτs) hMapOne (hW i).1
  have hUC2 (i : Fin A.count) : C2 (F05Q A i (T-s)) (pull A i U) := c2_add (hPC2 i) (hF i)
  have hTrace (x : M.Carrier) (_hx : x ∈ closure O) (t : ℝ) (ht : t ∈ Icc (r-s) (τ-s)) :
      U x t = V x t := by
    have hReconstruct := F05_reflected_zero_reconstruct (s := s) (τ := τ) (t := t+s) hb
      (by linarith [ht.2])
      (by simpa only [add_sub_cancel_right] using hbr.trans ht.1) p w x
    simpa only [add_sub_cancel_right,F05ManifoldTimeShift,U,V,F] using hReconstruct
  have hVEq := F05_manifold_time_shift_equation hA h (sub_pos.mpr hτs) hMapτ w
    (fun i => (hW i).1) hEquation
  have hNative := F05_physical_nonlinear_equation_transfer hA (fun t => h (t+s))
    (sub_lt_sub_right hrτ s) (sub_nonneg.mpr hsr.le) (sub_le_sub_right hτT.le s) le_rfl
    U V hUC2 hVC2 hTrace hVEq
  intro i z hz
  have hAt := hNative i z.val ⟨z.property.1,hz⟩
  have hPullU : pull A i U = fun q => pull A i (F05ManifoldTimeShift s p) q+pull A i F q := rfl
  rw [hPullU] at hAt
  exact F05_encoded_nonlinear_equation (flatA (h (z.val.2+s)) A i z.val)
    (flatB (h (z.val.2+s)) A i z.val) (scalarCurvature (h (z.val.2+s)) (lift A i z.val.1))
    (pull A i (F05ManifoldTimeShift s p)) (pull A i F) (hPC2 i) (hF i) (u.val i).val z
    (hEval i z).1 (hEval i z).2.1 (hEval i z).2.2.1 (hEval i z).2.2.2 hAt

end Yau.Proofs.F05Aux
