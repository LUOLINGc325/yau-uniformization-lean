import Yau.Proofs.F05BootstrapTranslatedEquation
import Yau.Proofs.F05BootstrapOperatorLinear
import Yau.Proofs.F05BootstrapRelativeRestriction

/-! The exact backward temporal quotient equation on the closed receiving
slab, including its terminal endpoint. Every sampled time is at most T. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05BackwardTimeQuotient (u : Point n → ℝ) (h : ℝ) (z : Point n) : ℝ :=
  h⁻¹*(u z-timeTranslate (-h) u z)

theorem F05_relative_backward_time_quotient_equation {X : Set (Space n)} {s0 s T h : ℝ}
    (hX : UniqueDiffOn ℝ X) (hsT : s < T) (hh : 0 ≤ h) (hStart : s0 ≤ s-h)
    {u f : Point n → ℝ} (hu : F05RelC2 X (Icc s0 T) u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (hPDE : ∀ z ∈ X ×ˢ Icc s0 T, F05RelOp X (Icc s0 T) a b u z = f z) :
    F05RelC2 X (Icc s T) (F05BackwardTimeQuotient u h) ∧
      ∀ z ∈ X ×ˢ Icc s T,
        let q := timeTranslatePoint (-h) z
        F05RelOp X (Icc s T) a b (F05BackwardTimeQuotient u h) z =
          h⁻¹*(f z-f q)+
          (∑ j,∑ k,(h⁻¹*(a z j k-a q j k))*F05RelDD X u q (realVec j) (realVec k))+
          ∑ j,(h⁻¹*(b z j-b q j))*F05RelD X u q (realVec j) := by
  have hI : Icc s T ⊆ Icc s0 T := fun t ht => ⟨by linarith [ht.1],ht.2⟩
  have hIS : Icc (s+(-h)) (T+(-h)) ⊆ Icc s0 T :=
    fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hTime := uniqueDiffOn_Icc hsT
  have hTimeS := uniqueDiffOn_Icc (show s+(-h) < T+(-h) by linarith)
  have huBase := F05_relative_c2_restrict hX hX hTime Subset.rfl hI hu
  have huLocal := F05_relative_c2_restrict hX hX hTimeS Subset.rfl hIS hu
  have huShift := F05_relative_c2_timeTranslate hsT huLocal
  have hDifference := F05_relative_c2_sub hX huBase huShift
  refine ⟨F05_relative_c2_const_mul hX hDifference h⁻¹,?_⟩
  intro z hz
  dsimp only
  let q := timeTranslatePoint (-h) z
  have hQ : q ∈ X ×ˢ Icc s0 T := by
    exact ⟨hz.1,hIS ⟨add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩⟩
  have hBaseJets := F05_relative_restriction_jets hX hX hTime Subset.rfl hI hu hz
  have hShiftJets := F05_relative_restriction_jets hX hX hTimeS Subset.rfl hIS hu
    (z := q) ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩
  have hTranslatedTime := F05_relative_timeTranslate_time_jet hsT huLocal hz
  have hShiftTime : F05RelT (Icc s T) (timeTranslate (-h) u) z = F05RelT (Icc s0 T) u q :=
    hTranslatedTime.trans hShiftJets.2.2
  have hBase : F05RelOp X (Icc s T) a b u z = f z := by
    simpa only [F05RelOp,hBaseJets.1,hBaseJets.2.1,hBaseJets.2.2] using hPDE z ⟨hz.1,hI hz.2⟩
  have hShift : F05RelOp X (Icc s T) a b (timeTranslate (-h) u) z =
      f q+(∑ j,∑ k,(a q j k-a z j k)*F05RelDD X u q (realVec j) (realVec k))+
        ∑ j,(b q j-b z j)*F05RelD X u q (realVec j) := by
    rw [F05RelOp,hShiftTime]
    change F05RelT (Icc s0 T) u q-(∑ j,∑ k,a z j k*F05RelDD X u q (realVec j) (realVec k))-
      (∑ j,b z j*F05RelD X u q (realVec j)) = _
    have hOriginal := hPDE q hQ
    dsimp only [F05RelOp] at hOriginal
    simp only [sub_mul,Finset.sum_sub_distrib]
    linarith
  have hSecond : (∑ j,∑ k,(h⁻¹*(a z j k-a q j k))*F05RelDD X u q (realVec j) (realVec k)) =
      -(h⁻¹*(∑ j,∑ k,(a q j k-a z j k)*F05RelDD X u q (realVec j) (realVec k))) := by
    simp_rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hFirst : (∑ j,(h⁻¹*(b z j-b q j))*F05RelD X u q (realVec j)) =
      -(h⁻¹*(∑ j,(b q j-b z j)*F05RelD X u q (realVec j))) := by
    simp_rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change F05RelOp X (Icc s T) a b (fun p => h⁻¹*(u p-timeTranslate (-h) u p)) z = _
  rw [F05_relative_operator_const_mul hX hDifference h⁻¹ a b hz,
    F05_relative_operator_sub hX huBase huShift a b hz,hBase,hShift,hSecond,hFirst]
  ring

end Yau.Proofs.F05Aux
