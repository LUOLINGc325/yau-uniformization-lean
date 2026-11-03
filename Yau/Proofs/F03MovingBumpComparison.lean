import Yau.Proofs.F03MovingBumpDecay
import Yau.Proofs.F03ParabolicC2

/-! The actual exponentially weighted cubic can be compared with classical heat. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem movingBump_comparison {n : ℕ} {O : Set (Space n)} {T lam upper R V ε : ℝ}
    (hO : IsOpen O) (hcO : IsCompact (closure O)) (hT : 0 < T) (hR : 0 < R) (hε : 0 ≤ ε)
    {a : Point n → Mat n} (hEll : Elliptic (cylinder (closure O) 0 T) a lam upper)
    {c : ℝ → Space n} (hc : ContDiff ℝ 2 c)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, ‖deriv c t‖ ≤ V)
    (hTube : ∀ x ∈ frontier O, ∀ t ∈ Icc (0 : ℝ) T, R ≤ ‖x-c t‖)
    {u : Point n → ℝ} (hu : C2 (cylinder (closure O) 0 T) u)
    (hu0 : ∀ p ∈ cylinder (closure O) 0 T, 0 ≤ u p)
    (hHeat : ∀ p ∈ O ×ˢ Ioc (0 : ℝ) T,
      linearOp (cylinder (closure O) 0 T) a (fun _ _ => 0) u p=0)
    (hInit : ∀ x ∈ closure O, ε*movingBallBump R c (x,0) ≤ u (x,0)) :
    let C := movingCubicRate R lam (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper)
    ∀ p ∈ cylinder (closure O) 0 T, decayingMovingBump ε C 0 R c p ≤ u p := by
  let C := movingCubicRate R lam (2*R*V+2*(Fintype.card (RIdx n) : ℝ)*upper)
  let w := decayingMovingBump ε C 0 R c
  have hw : C2 (cylinder (closure O) 0 T) w :=
    parabolic_c2_of_joint_contDiffOn hT isOpen_univ
      (decayingMovingBump_contDiff ε C 0 R hc).contDiffOn (subset_univ _)
  have hwd (p : Point n) : DifferentiableAt ℝ (fun s => w (p.1,s)) p.2 :=
    (decayingMovingBump_time_hasDerivAt ε C 0 R p.1
      (hc.differentiable (by norm_num) p.2).hasDerivAt).differentiableAt
  have hTime (p : Point n) (hp : p ∈ cylinder (closure O) 0 T) :
      timeD (cylinder (closure O) 0 T) w p=deriv (fun s => w (p.1,s)) p.2 := by
    have hFiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T}=Icc (0 : ℝ) T := by
      ext t
      simp only [cylinder,mem_prod,hp.1,true_and,mem_setOf_eq]
    unfold timeD
    rw [hFiber]
    exact (hwd p).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  apply comparison_principle hO hcO hT hw hu hEll
  · intro x hx
    simpa only [w,decayingMovingBump,sub_zero,mul_zero,neg_zero,Real.exp_zero,mul_one] using hInit x hx
  · intro x hx t ht
    have hz : w (x,t)=0 := decayingMovingBump_zero_off hR.le ε C 0 c x t (hTube x hx t ht)
    rw [hz]
    exact hu0 (x,t) ⟨frontier_subset_closure hx,ht⟩
  · intro p hp
    rw [hHeat p hp]
    unfold linearOp
    have hpQ : p ∈ cylinder (closure O) 0 T := ⟨subset_closure hp.1,hp.2.1.le,hp.2.2⟩
    rw [hTime p hpQ]
    simp only [zero_mul,Finset.sum_const_zero,sub_zero]
    exact decayingMovingBump_subcaloric hEll hR hε 0 p hpQ
      (hc.differentiable (by norm_num) p.2).hasDerivAt (hV p.2 hpQ.2)

end Yau.Proofs.F03Aux
