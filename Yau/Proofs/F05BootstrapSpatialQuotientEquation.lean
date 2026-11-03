import Yau.Proofs.F05BootstrapRelativeTranslation
import Yau.Proofs.F05BootstrapOperatorLinear
import Yau.Proofs.F05BootstrapRelativeRestriction

/-! Exact forward spatial quotient equation on a buffered physical set.
The coefficient differences multiply the full shifted spatial jets. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_spatial_quotient_equation {X Y : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) (hY : UniqueDiffOn ℝ Y) (hI : UniqueDiffOn ℝ I)
    (hXY : X ⊆ Y) (e : Space n) (h : ℝ) (hMap : MapsTo (fun x => x+h • e) X Y)
    {u f : Point n → ℝ} (hu : F05RelC2 Y I u)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (hPDE : ∀ z ∈ Y ×ˢ I, F05RelOp Y I a b u z = f z) :
    F05RelC2 X I (spatialDifferenceQuotient u e h) ∧
      ∀ z ∈ X ×ˢ I,
        let q := spatialTranslatePoint (h • e) z
        F05RelOp X I a b (spatialDifferenceQuotient u e h) z =
          h⁻¹*(f q-f z)+
          (∑ j,∑ k,(h⁻¹*(a q j k-a z j k))*F05RelDD Y u q (realVec j) (realVec k))+
          ∑ j,(h⁻¹*(b q j-b z j))*F05RelD Y u q (realVec j) := by
  have huX := F05_relative_c2_restrict hY hX hI hXY Subset.rfl hu
  have huShift := F05_relative_c2_spatialTranslate hX hY (h • e) hMap hu
  have hDifference := F05_relative_c2_sub hX huShift huX
  refine ⟨F05_relative_c2_const_mul hX hDifference h⁻¹,?_⟩
  intro z hz
  dsimp only
  let q := spatialTranslatePoint (h • e) z
  have hQ : q ∈ Y ×ˢ I := ⟨hMap hz.1,hz.2⟩
  have hJets := F05_relative_spatialTranslate_jets hX hY (h • e) hMap hu hz
  have hBaseJets := F05_relative_restriction_jets hY hX hI hXY Subset.rfl hu hz
  have hBase : F05RelOp X I a b u z = f z := by
    simpa only [F05RelOp,hBaseJets.1,hBaseJets.2.1,hBaseJets.2.2] using hPDE z ⟨hXY hz.1,hz.2⟩
  have hShift : F05RelOp X I a b (spatialTranslate (h • e) u) z =
      f q+(∑ j,∑ k,(a q j k-a z j k)*F05RelDD Y u q (realVec j) (realVec k))+
        ∑ j,(b q j-b z j)*F05RelD Y u q (realVec j) := by
    rw [F05RelOp,hJets.1,hJets.2.1,hJets.2.2]
    have hOriginal := hPDE q hQ
    dsimp only [F05RelOp] at hOriginal
    simp only [sub_mul,Finset.sum_sub_distrib]
    linarith
  have hSecond : (∑ j,∑ k,(h⁻¹*(a q j k-a z j k))*F05RelDD Y u q (realVec j) (realVec k)) =
      h⁻¹*(∑ j,∑ k,(a q j k-a z j k)*F05RelDD Y u q (realVec j) (realVec k)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hFirst : (∑ j,(h⁻¹*(b q j-b z j))*F05RelD Y u q (realVec j)) =
      h⁻¹*(∑ j,(b q j-b z j)*F05RelD Y u q (realVec j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change F05RelOp X I a b (fun p => h⁻¹*(spatialTranslate (h • e) u p-u p)) z = _
  rw [F05_relative_operator_const_mul hX hDifference h⁻¹ a b hz,
    F05_relative_operator_sub hX huShift huX a b hz,hShift,hBase,hSecond,hFirst]
  ring

end Yau.Proofs.F05Aux
