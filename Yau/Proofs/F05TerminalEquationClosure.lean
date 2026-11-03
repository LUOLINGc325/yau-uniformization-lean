import Yau.Proofs.F05BootstrapNative

/-! The original nonlinear equation reaches a terminal time from strict
earlier times by continuity of the actual C2 jets. No equation is imposed
on the reflected approximants after their moving endpoints. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_closed_time_eq {Z V : Type*} [TopologicalSpace Z] [TopologicalSpace V] [T2Space V]
    {X : Set Z} {r T : ℝ} (hrT : r < T) {f g : Z × ℝ → V}
    (hf : ContinuousOn f (X ×ˢ Icc r T)) (hg : ContinuousOn g (X ×ˢ Icc r T))
    (hEq : EqOn f g (X ×ˢ Ico r T)) : EqOn f g (X ×ˢ Icc r T) := by
  intro z hz
  have hF : ContinuousOn (fun t => f (z.1,t)) (Icc r T) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hz.1,ht⟩)
  have hG : ContinuousOn (fun t => g (z.1,t)) (Icc r T) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hz.1,ht⟩)
  have hClosed := isClosed_Icc.isClosed_eq hF hG
  have hSub : Ico r T ⊆ {t ∈ Icc r T | f (z.1,t) = g (z.1,t)} :=
    fun t ht => ⟨⟨ht.1,ht.2.le⟩,hEq ⟨hz.1,ht⟩⟩
  have hClosure := closure_minimal hSub hClosed
  have hzCl : z.2 ∈ closure (Ico r T) := by
    rw [closure_Ico hrT.ne]
    exact hz.2
  exact (hClosure hzCl).2

theorem F05_nonlinear_equation_terminal_closure {n : ℕ} {X : Set (Space n)} {r T : ℝ}
    (hr : 0 ≤ r) (hrT : r < T) {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R : Point n → ℝ)
    (hA : ∀ i j, ContinuousOn (fun z => A z i j) (cylinder X 0 T))
    (hB : ∀ i, ContinuousOn (fun z => B z i) (cylinder X 0 T))
    (hR : ContinuousOn R (cylinder X 0 T))
    (hEq : ∀ z ∈ X ×ˢ Ico r T,
      timeD (cylinder X 0 T) u z = Real.exp (-u z)*
        ((∑ i,∑ j,A z i j*spatialDD u z (realVec i) (realVec j))+
          ∑ i,B z i*spatialD u z (realVec i))+(1-Real.exp (-u z))*R z) :
    ∀ z ∈ X ×ˢ Icc r T,
      timeD (cylinder X 0 T) u z = Real.exp (-u z)*
        ((∑ i,∑ j,A z i j*spatialDD u z (realVec i) (realVec j))+
          ∑ i,B z i*spatialD u z (realVec i))+(1-Real.exp (-u z))*R z := by
  have hSub : X ×ˢ Icc r T ⊆ cylinder X 0 T := fun z hz => ⟨hz.1,hr.trans hz.2.1,hz.2.2⟩
  have hHess (i j : RIdx n) : ContinuousOn
      (fun z => spatialDD u z (realVec i) (realVec j)) (cylinder X 0 T) :=
    (hu.2.2.1.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hGrad (i : RIdx n) : ContinuousOn (fun z => spatialD u z (realVec i)) (cylinder X 0 T) :=
    hu.2.1.clm_apply continuousOn_const
  have hMain := continuousOn_finsetSum Finset.univ (fun i _ =>
    continuousOn_finsetSum Finset.univ (fun j _ =>
    (hA i j).mul (hHess i j)))
  have hDrift := continuousOn_finsetSum Finset.univ (fun i _ => (hB i).mul (hGrad i))
  have hExp := Real.continuous_exp.comp_continuousOn hu.1.neg
  exact F05_closed_time_eq hrT (hu.2.2.2.1.mono hSub)
    (((hExp.mul (hMain.add hDrift)).add ((continuousOn_const.sub hExp).mul hR)).mono hSub) hEq

end Yau.Proofs.F05Aux
