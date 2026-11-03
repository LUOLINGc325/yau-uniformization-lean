import Yau.Proofs.F05BootstrapDefinitions
import Yau.LeafProofs.L16LocalTimeTransport

/-! Time translation preserves the actual one-sided relative jets and
Schauder bounds on the translated closed slab, including its top endpoint. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_timeTranslate_time_jet {X : Set (Space n)} {l r τ : ℝ}
    (hlr : l < r) {v : Point n → ℝ}
    (hv : F05RelC2 X (Icc (l+τ) (r+τ)) v) {z : Point n} (hz : z ∈ X ×ˢ Icc l r) :
    F05RelT (Icc l r) (timeTranslate τ v) z =
      F05RelT (Icc (l+τ) (r+τ)) v (timeTranslatePoint τ z) := by
  have hDiff := hv.2.2.2.2.2 (timeTranslatePoint τ z)
    ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩
  exact (hasDerivWithinAt_timeTranslate (u := v) (τ := τ) ⟨mem_univ _,hz.2⟩ hDiff).derivWithin
    (uniqueDiffOn_Icc hlr z.2 hz.2)

theorem F05_relative_c2_timeTranslate {X : Set (Space n)} {l r τ : ℝ}
    (hlr : l < r) {v : Point n → ℝ} (hv : F05RelC2 X (Icc (l+τ) (r+τ)) v) :
    F05RelC2 X (Icc l r) (timeTranslate τ v) := by
  have hMap : MapsTo (timeTranslatePoint τ) (X ×ˢ Icc l r) (X ×ˢ Icc (l+τ) (r+τ)) :=
    fun z hz => ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩
  have hC : ContinuousOn (timeTranslatePoint τ) (X ×ˢ Icc l r) :=
    (timeTranslatePoint_contDiff (n := n) τ).continuous.continuousOn
  refine ⟨hv.1.comp hC hMap,hv.2.1.comp hC hMap,hv.2.2.1.comp hC hMap,?_,?_,?_⟩
  · exact (hv.2.2.2.1.comp hC hMap).congr
      (fun z hz => F05_relative_timeTranslate_time_jet hlr hv hz)
  · intro t ht
    exact hv.2.2.2.2.1 (t+τ) ⟨add_le_add ht.1 le_rfl,add_le_add ht.2 le_rfl⟩
  · intro z hz
    have hDiff := hv.2.2.2.2.2 (timeTranslatePoint τ z) (hMap hz)
    exact (hasDerivWithinAt_timeTranslate (u := v) (τ := τ) ⟨mem_univ _,hz.2⟩ hDiff).differentiableWithinAt

theorem F05_relative_schauder_timeTranslate {X : Set (Space n)} {l r τ α C : ℝ}
    (hlr : l < r) {v : Point n → ℝ} (hv : F05RelSchauder α X (Icc (l+τ) (r+τ)) v C) :
    F05RelSchauder α X (Icc l r) (timeTranslate τ v) C := by
  refine ⟨F05_relative_c2_timeTranslate hlr hv.1,
    holderBound_timeTranslate_on_space hv.2.1,holderBound_timeTranslate_on_space hv.2.2.1,?_⟩
  exact holderBound_congr_on (holderBound_timeTranslate_on_space hv.2.2.2)
    (fun z hz => (F05_relative_timeTranslate_time_jet hlr hv.1 hz).symm)

end Yau.Proofs.F05Aux
