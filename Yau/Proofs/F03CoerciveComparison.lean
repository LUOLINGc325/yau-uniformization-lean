import Yau.Proofs.F03DirichletEnergyIdentity

/-! Coercive comparison in the actual supported physical energy space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem l2_inner_difference_nonpos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F G w : Lp ℝ 2 μ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hFG : ∀ᵐ x ∂μ, 0 < w x → F x ≤ G x) :
    inner ℝ (F-G) w ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hw,hFG,Lp.coeFn_sub F G] with x hx hle hsub
  rw [hsub,Pi.sub_apply]
  simp only [RCLike.inner_apply,conj_trivial]
  by_cases hp : 0 < w x
  · exact mul_nonpos_of_nonneg_of_nonpos hx (sub_nonpos.mpr (hle hp))
  · have hz : w x=0 := le_antisymm (le_of_not_gt hp) hx
    simp only [hz,zero_mul,Pi.zero_apply,le_refl]

theorem dirichlet_coercive_difference_norm (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    (u w : DirichletEnergy g μ hμ Ω)
    (qH F G : Lp ℝ 2 (μ.restrict Ω)) (qD : LeafProofs.L03.L2FormHilbert g (μ.restrict Ω) 1)
    (hu : inner ℝ u w=inner ℝ F (dirichletL2 g μ hμ Ω w))
    (hq : inner ℝ qH (dirichletL2 g μ hμ Ω w)+
      (1/2 : ℝ)*inner ℝ qD (dirichletD g μ hμ Ω w)=inner ℝ G (dirichletL2 g μ hμ Ω w))
    (hJ : inner ℝ (dirichletL2 g μ hμ Ω u-qH) (dirichletL2 g μ hμ Ω w)=
      ‖dirichletL2 g μ hμ Ω w‖^2)
    (hD : inner ℝ (dirichletD g μ hμ Ω u-qD) (dirichletD g μ hμ Ω w)=
      ‖dirichletD g μ hμ Ω w‖^2) :
    ‖w‖^2=inner ℝ (F-G) (dirichletL2 g μ hμ Ω w) := by
  have hnorm := dirichletEnergy_inner g μ hμ Ω w w
  simp only [real_inner_self_eq_norm_sq] at hnorm
  rw [dirichletEnergy_inner] at hu
  rw [inner_sub_left] at hJ hD ⊢
  linarith only [hnorm,hu,hq,hJ,hD]

theorem dirichlet_coercive_test_zero (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    (w : DirichletEnergy g μ hμ Ω) (F G : Lp ℝ 2 (μ.restrict Ω))
    (hnorm : ‖w‖^2=inner ℝ (F-G) (dirichletL2 g μ hμ Ω w))
    (hw : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ dirichletL2 g μ hμ Ω w x)
    (hFG : ∀ᵐ x ∂μ.restrict Ω, 0 < dirichletL2 g μ hμ Ω w x → F x ≤ G x) :
    w=0 := by
  have hnonpos := l2_inner_difference_nonpos (μ.restrict Ω) F G (dirichletL2 g μ hμ Ω w) hw hFG
  rw [← hnorm] at hnonpos
  apply norm_eq_zero.mp
  nlinarith only [hnonpos,norm_nonneg w]

end Yau.Proofs.F03Aux
