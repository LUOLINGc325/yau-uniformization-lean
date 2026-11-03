import Yau.LeafProofs.L23DistanceEnergyIntegral
import Yau.LeafProofs.L23DistanceEnergyVariation

/-! Actual first and second parameter derivatives pass through compact energy integrals. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def parameterDirection (F : E × ℝ → ℝ) (a : E) (p : E × ℝ) : ℝ :=
  parameterDerivative F p a

theorem parameterDirection_contDiffOn {F : E × ℝ → ℝ} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (k : ℕ)
    (hF : ContDiffOn ℝ (k+1) F (U ×ˢ J)) (a : E) :
    ContDiffOn ℝ k (parameterDirection F a) (U ×ˢ J) :=
  (parameterDerivative_contDiffOn hU hJ k hF).clm_apply contDiffOn_const

theorem unitIntegral_firstDirection {F : E × ℝ → ℝ} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ J)) {x : E} (hx : x∈U) (a : E) :
    mapDirection (fun y => ∫ u in Set.Icc (0 : ℝ) 1, F (y,u)) a x=
      ∫ u in Set.Icc (0 : ℝ) 1, parameterDirection F a (x,u) := by
  have hDP : ContinuousOn (fun u => parameterDerivative F (x,u)) (Set.Icc (0 : ℝ) 1) :=
    (parameterDerivative_contDiffOn hU hJ 0 (by simpa using hF)).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hu => ⟨hx,hIJ hu⟩)
  have hDPint : IntegrableOn (fun u => parameterDerivative F (x,u)) (Set.Icc (0 : ℝ) 1) :=
    hDP.integrableOn_Icc
  unfold mapDirection
  rw [(hasFDerivAt_unitIntegral hU hJ hIJ hF hx).fderiv,
    ContinuousLinearMap.integral_apply hDPint]
  rfl

theorem unitIntegral_secondDirection {F : E × ℝ → ℝ} {U : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hJ : IsOpen J) (hIJ : Set.Icc (0 : ℝ) 1 ⊆ J)
    (hF : ContDiffOn ℝ 2 F (U ×ˢ J)) {x : E} (hx : x∈U) (a b : E) :
    mapDirection (mapDirection (fun y => ∫ u in Set.Icc (0 : ℝ) 1, F (y,u)) a) b x=
      ∫ u in Set.Icc (0 : ℝ) 1, parameterDirection (parameterDirection F a) b (x,u) := by
  have hF₁ : ContDiffOn ℝ 1 F (U ×ˢ J) := hF.of_le (by norm_num)
  have heq : mapDirection (fun y => ∫ u in Set.Icc (0 : ℝ) 1, F (y,u)) a=ᶠ[𝓝 x]
      (fun y => ∫ u in Set.Icc (0 : ℝ) 1, parameterDirection F a (y,u)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact unitIntegral_firstDirection hU hJ hIJ hF₁ hy a
  rw [mapDirection_congr heq b]
  exact unitIntegral_firstDirection hU hJ hIJ (parameterDirection_contDiffOn hU hJ 1 hF a) hx b

end Yau.LeafProofs.L23Aux
