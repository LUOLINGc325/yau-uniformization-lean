import Yau.Proofs.F03ParabolicC2

/-! Actual closed-cylinder transport of a positive-time classical heat germ. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def positiveTimeShift {n : ℕ} (s : ℝ) (u : Point n → ℝ) (p : Point n) : ℝ :=
  u (p.1,s+p.2)

theorem positiveTimeShift_C2 {n : ℕ} {O K : Set (Space n)} (hO : IsOpen O)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi (0 : ℝ)))
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) (hKO : K ⊆ O) :
    C2 (cylinder K 0 T) (positiveTimeShift s u) := by
  let f : Point n → Point n := fun p => (p.1,s+p.2)
  have hf : ContDiff ℝ ∞ f := by dsimp only [f]; fun_prop
  have hQ : IsOpen (f ⁻¹' (O ×ˢ Ioi (0 : ℝ))) := (hO.prod isOpen_Ioi).preimage hf.continuous
  have hcomp := hu.comp hf.contDiffOn (show MapsTo f (f ⁻¹' (O ×ˢ Ioi (0 : ℝ)))
    (O ×ˢ Ioi (0 : ℝ)) from fun _ hp => hp)
  apply parabolic_c2_of_joint_contDiffOn hT hQ (hcomp.of_le (by simp))
  intro p hp
  exact ⟨hKO hp.1,add_pos_of_pos_of_nonneg hs hp.2.1⟩

theorem positiveTimeShift_linearOp {n : ℕ} {O K : Set (Space n)} (hO : IsOpen O)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi (0 : ℝ)))
    (a : Point n → Mat n) {s T : ℝ} (hs : 0 < s) (hT : 0 < T) (hKO : K ⊆ O)
    (p : Point n) (hp : p ∈ cylinder K 0 T) :
    linearOp (cylinder K 0 T) (fun q => a (q.1,s+q.2)) (fun _ _ => 0) (positiveTimeShift s u) p =
      linearOp (O ×ˢ Ioi (0 : ℝ)) a (fun _ _ => 0) u (p.1,s+p.2) := by
  have hq : (p.1,s+p.2) ∈ O ×ˢ Ioi (0 : ℝ) :=
    ⟨hKO hp.1,add_pos_of_pos_of_nonneg hs hp.2.1⟩
  have hda : DifferentiableAt ℝ (fun t => u (p.1,t)) (s+p.2) :=
    ((hu.contDiffAt ((hO.prod isOpen_Ioi).mem_nhds hq)).comp (s+p.2)
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hd : HasDerivAt (fun t => positiveTimeShift s u (p.1,t))
      (deriv (fun t => u (p.1,t)) (s+p.2)) p.2 := by
    have h := hda.hasDerivAt.comp p.2 ((hasDerivAt_id p.2).const_add s)
    simpa only [positiveTimeShift,Function.comp_def,id_eq,mul_one] using h
  have hFiber : {t | (p.1,t) ∈ cylinder K 0 T}=Icc (0 : ℝ) T := by
    ext t
    simp only [cylinder,mem_prod,hp.1,true_and,mem_setOf_eq]
  have hTime : timeD (cylinder K 0 T) (positiveTimeShift s u) p =
      deriv (fun t => u (p.1,t)) (s+p.2) := by
    unfold timeD
    rw [hFiber]
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  unfold linearOp
  rw [hTime,timeD_eq_deriv_of_isOpen (hO.prod isOpen_Ioi) hq]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  rfl

end Yau.Proofs.F03Aux
