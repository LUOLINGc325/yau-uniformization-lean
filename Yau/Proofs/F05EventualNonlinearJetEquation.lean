import Yau.Proofs.F05JetComponents

/-! The original nonlinear equation passes through actual convergent jets
when each fixed point satisfies the equation eventually. Reflected values
beyond the moving endpoints are never required to satisfy the equation. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_eventual_nonlinear_jet_equation (A : Mat n) (B : RIdx n → ℝ) (R : ℝ)
    (u : ℕ → ℝ) (D : ℕ → F05Dual n) (H : ℕ → F05Hessian n) (J : ℕ → ℝ)
    {uLim : ℝ} {DLim : F05Dual n} {HLim : F05Hessian n} {JLim : ℝ}
    (hU : Tendsto u atTop (𝓝 uLim)) (hD : Tendsto D atTop (𝓝 DLim))
    (hH : Tendsto H atTop (𝓝 HLim)) (hJ : Tendsto J atTop (𝓝 JLim))
    (hEq : ∀ᶠ k in atTop, J k = Real.exp (-u k)*
      ((∑ i,∑ j,A i j*H k (realVec i) (realVec j))+∑ i,B i*D k (realVec i))+
        (1-Real.exp (-u k))*R) :
    JLim = Real.exp (-uLim)*
      ((∑ i,∑ j,A i j*HLim (realVec i) (realVec j))+∑ i,B i*DLim (realVec i))+
        (1-Real.exp (-uLim))*R := by
  have hHEval (i j : RIdx n) : Continuous (fun F : F05Hessian n => F (realVec i) (realVec j)) :=
    ((ContinuousLinearMap.apply ℝ ℝ (realVec j)).comp
      (ContinuousLinearMap.apply ℝ (F05Dual n) (realVec i))).continuous
  have hDEval (i : RIdx n) : Continuous (fun F : F05Dual n => F (realVec i)) :=
    (ContinuousLinearMap.apply ℝ ℝ (realVec i)).continuous
  have hMain : Tendsto (fun k => ∑ i,∑ j,A i j*H k (realVec i) (realVec j)) atTop
      (𝓝 (∑ i,∑ j,A i j*HLim (realVec i) (realVec j))) :=
    tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
      (fun j _ => tendsto_const_nhds.mul (((hHEval i j).tendsto HLim).comp hH)))
  have hDrift : Tendsto (fun k => ∑ i,B i*D k (realVec i)) atTop
      (𝓝 (∑ i,B i*DLim (realVec i))) :=
    tendsto_finsetSum Finset.univ
      (fun i _ => tendsto_const_nhds.mul (((hDEval i).tendsto DLim).comp hD))
  have hExp : Tendsto (fun k => Real.exp (-u k)) atTop (𝓝 (Real.exp (-uLim))) :=
    (Real.continuous_exp.tendsto (-uLim)).comp hU.neg
  have hRHS := (hExp.mul (hMain.add hDrift)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hExp).mul (tendsto_const_nhds (x := R)))
  exact tendsto_nhds_unique hJ (hRHS.congr' (hEq.mono fun k hk => hk.symm))

end Yau.Proofs.F05Aux
