import Yau.LeafProofs.L17ParabolicUniquenessCalculus

open Set Metric Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicUniquenessAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

def damped (u : SchauderSpace P T gamma hT) (q : Cylinder M T) : ℝ :=
  Real.exp (-(q.2 : ℝ))*schauderFun u q

def dampedTime (u : SchauderSpace P T gamma hT) (q : Cylinder M T) : ℝ :=
  Real.exp (-(q.2 : ℝ))*(timeFun u q-schauderFun u q)

theorem damped_continuous (u : SchauderSpace P T gamma hT) : Continuous (damped u) :=
  (((continuous_subtype_val.comp continuous_snd).neg).rexp).mul (schauderFun_continuous u)

theorem damped_abs_le (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    |damped u q| ≤ P.radius^2*‖u‖ := by
  have he : Real.exp (-(q.2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr q.2.property.1)
  calc
    _ = Real.exp (-(q.2 : ℝ))*|schauderFun u q| := by
      rw [damped, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1*|schauderFun u q| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using (function_holder_bounds u).1 q

theorem damped_initial (u : SchauderSpace P T gamma hT) (x : M.Carrier) :
    damped u (x,⟨0,⟨le_rfl,hT.le⟩⟩) = 0 := by
  simp [damped, schauderFun_initial]

theorem damped_hasDerivWithinAt (u : SchauderSpace P T gamma hT)
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun tau => Real.exp (-tau)*schauderFun u (closedTimePath T hT x tau))
      (dampedTime u (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  have he := (((hasDerivAt_id (t : ℝ)).neg).exp).hasDerivWithinAt (s := Icc (0 : ℝ) T)
  have hh := he.mul (schauderFun_hasDerivWithinAt u x t)
  change HasDerivWithinAt (fun tau => Real.exp (-tau)*schauderFun u (closedTimePath T hT x tau))
    (Real.exp (-(t : ℝ))*(-1)*schauderFun u (closedTimePath T hT x t)+
      Real.exp (-(t : ℝ))*timeFun u (x,t)) (Icc (0 : ℝ) T) (t : ℝ) at hh
  convert hh using 1
  dsimp only [dampedTime,closedTimePath]
  rw [projIcc_val]
  ring

theorem damped_background_contDiffAt (u : SchauderSpace P T gamma hT)
    (p : M.Carrier) (t : Time T) {z : ComplexVector n}
    (hz : z ∈ (P.charts.chart p).source) :
    ContDiffAt ℝ 2 (fun w => damped u (P.charts.chart p w,t)) z := by
  change ContDiffAt ℝ 2 (fun w => Real.exp (-(t : ℝ))*schauderFun u (P.charts.chart p w,t)) z
  exact contDiffAt_const.mul (backgroundChart_comp_contDiffAt _ (P.charts.differentiable p)
    _ hz (actualFunction_native_contDiffAt u _ t))

theorem damped_equation (u : SchauderSpace P T gamma hT)
    (hu : ∀ q : Cylinder M T,
      timeFun u q-laplacian g (fun y => schauderFun u (y,q.2)) q.1 = 0)
    (p : M.Carrier) (t : Time T) {z : ComplexVector n}
    (hz : z ∈ (P.charts.chart p).source) :
    dampedTime u (P.charts.chart p z,t)-
      realHessianContraction (scalarSymbol (pullbackMatrix g (P.charts.chart p) z))
        (fun w => damped u (P.charts.chart p w,t)) z =
      -damped u (P.charts.chart p z,t) := by
  have hf := backgroundChart_comp_contDiffAt _ (P.charts.differentiable p)
    (fun y => schauderFun u (y,t)) hz (actualFunction_native_contDiffAt u _ t)
  have hl := laplacian_eq_backgroundChart_scalarSymbol g (P.charts.chart p)
    (P.charts.differentiable p) (P.charts.inverse_differentiable p)
    (fun y => schauderFun u (y,t)) hz (actualFunction_native_contDiffAt u _ t)
  change Real.exp (-(t : ℝ))*(timeFun u (P.charts.chart p z,t)-schauderFun u (P.charts.chart p z,t))-
    realHessianContraction _ (fun w => Real.exp (-(t : ℝ))*schauderFun u (P.charts.chart p w,t)) z = _
  rw [contraction_const_mul hf, ← hl]
  have hh := hu (P.charts.chart p z,t)
  change timeFun u (P.charts.chart p z,t)-laplacian g (fun y => schauderFun u (y,t)) (P.charts.chart p z) = 0 at hh
  dsimp [damped]
  rw [sub_eq_zero.mp hh]
  ring

end Yau.LeafProofs.L17ParabolicUniquenessAux
