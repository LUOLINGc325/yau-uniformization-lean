import Yau.LeafProofs.L17ParabolicUniquenessNonpositive

open Set Metric
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicUniquenessAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

local instance uniqueness_add_group : AddCommGroup (SchauderSpace P T gamma hT) :=
  (schauderSpace_normedAddCommGroup P T gamma hT).toAddCommGroup
local instance uniqueness_normed_space : NormedSpace ℝ (SchauderSpace P T gamma hT) :=
  schauderSpace_normedSpace P T gamma hT

theorem schauderFun_neg_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (-u) q = -schauderFun u q :=
  congrArg (fun f : BoundedContinuousFunction (Cylinder M T) ℝ => f q)
    ((functionCLM P T gamma hT).map_neg u)

theorem timeFun_neg_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    timeFun (-u) q = -timeFun u q :=
  congrArg (fun f : BoundedContinuousFunction (Cylinder M T) ℝ => f q)
    ((timeCLM P T gamma hT).map_neg u)

theorem actualLaplacian_neg_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    laplacian g (fun y => schauderFun (-u) (y,q.2)) q.1 =
      -laplacian g (fun y => schauderFun u (y,q.2)) q.1 := by
  obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
  rw [← hzx, selected_chart_laplacian, selected_chart_laplacian]
  have hh : hessianFun (-u) ⟨p,(z,q.2)⟩ = -hessianFun u ⟨p,(z,q.2)⟩ :=
    congrArg (fun f : BoundedContinuousFunction (LocalCylinder P T) (D2 n) => f ⟨p,(z,q.2)⟩)
      ((hessianCLM P T gamma hT).map_neg u)
  rw [hh,map_neg]

/-- Bounded zero-initial actual solutions of the original scalar parabolic
operator vanish, for every Holder exponent and including closed time endpoints. -/
theorem eq_zero_of_scalar_parabolic_equation
    (u : SchauderSpace P T gamma hT)
    (hu : ∀ q : Cylinder M T,
      timeFun u q-laplacian g (fun y => schauderFun u (y,q.2)) q.1 = 0) : u = 0 := by
  have hn : ∀ q : Cylinder M T,
      timeFun (-u) q-laplacian g (fun y => schauderFun (-u) (y,q.2)) q.1 = 0 := by
    intro q
    rw [timeFun_neg_value,actualLaplacian_neg_value]
    linarith [hu q]
  apply schauderFun_injective
  funext q
  have hp := damped_nonpositive u hu q
  have hm := damped_nonpositive (-u) hn q
  rw [damped,schauderFun_neg_value] at hm
  dsimp only [damped] at hp
  have he := Real.exp_pos (-(q.2 : ℝ))
  have hv : schauderFun u q = 0 := by nlinarith
  change schauderFun u q = schauderFun (0 : SchauderSpace P T gamma hT) q
  rw [hv]
  exact (congrArg (fun f : BoundedContinuousFunction (Cylinder M T) ℝ => f q)
    (functionCLM P T gamma hT).map_zero).symm

/-- Genuine injectivity of the actual continuous linear scalar parabolic map. -/
theorem scalarParabolicCLM_injective (hTime : T ≤ P.radius^2)
    (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1) :
    Function.Injective (scalarParabolicCLM P T gamma hT hTime hgamma hr) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply eq_zero_of_scalar_parabolic_equation
  intro q
  have hmap : scalarParabolicCLM P T gamma hT hTime hgamma hr (u-v) = 0 := by
    calc
      _ = scalarParabolicCLM P T gamma hT hTime hgamma hr u-
          scalarParabolicCLM P T gamma hT hTime hgamma hr v :=
        (scalarParabolicCLM P T gamma hT hTime hgamma hr).map_sub u v
      _ = 0 := by rw [huv,sub_self]
  have hh := congrArg (fun f : HolderSpace P T gamma => holderFun f q) hmap
  rw [scalarParabolicCLM_value] at hh
  exact hh.trans (by rfl)

end Yau.LeafProofs.L17ParabolicUniquenessAux
