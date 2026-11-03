import Yau.Proofs.F05RelativeNonlinearRestriction
import Yau.Proofs.F05BootstrapRelativeTimeTranslation

/-! A single actual closed relative Schauder slab supplies all local
positive-time receiving estimates, and its exact nonlinear equation
transports through a genuine time translation. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_closed_schauder_local (ν : Option (RIdx n)) {T α C : ℝ}
    (hC : 0 ≤ C) {u : Point n → ℝ} (hu : F05RelSchauder α (region ν 2) (Icc 0 T) u C) :
    F05LocalSchauder α ν T u := by
  intro r hr hr2 s hs hsT
  have hRel := F05_relative_schauder_restrict (F05_region_uniqueDiffOn ν (by norm_num))
    (F05_region_uniqueDiffOn ν hr) (uniqueDiffOn_Icc hsT)
    (F05_region_mono hr2.le) (show Icc s T ⊆ Icc 0 T from fun t ht => ⟨hs.le.trans ht.1,ht.2⟩) hu
  have hBudget : C ≤ 1+C := by linarith
  exact ⟨1+C,by linarith,hRel.1,holderBound_mono_const hRel.2.1 hBudget,
    holderBound_mono_const hRel.2.2.1 hBudget,holderBound_mono_const hRel.2.2.2 hBudget⟩

theorem F05_relative_nonlinear_time_translate (ν : Option (RIdx n)) {r l t τ : ℝ}
    (hlt : l < t) {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R u : Point n → ℝ}
    (hu : F05RelC2 (region ν r) (Icc (l+τ) (t+τ)) u)
    (hEq : F05RelativeNonlinearEquation ν r (l+τ) (t+τ) a b R u) :
    F05RelativeNonlinearEquation ν r l t (timeTranslate τ a)
      (fun z j => b (timeTranslatePoint τ z) j) (timeTranslate τ R) (timeTranslate τ u) := by
  intro z hz
  rw [F05_relative_timeTranslate_time_jet hlt hu hz]
  exact hEq (timeTranslatePoint τ z)
    ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩

end Yau.Proofs.F05Aux
