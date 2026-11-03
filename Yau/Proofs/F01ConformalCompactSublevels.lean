import Yau.Proofs.F01ComponentCompactCore
import Yau.Proofs.F01ConformalProfile

/-! The explicit conformal boundary profile has genuinely compact
sublevels on the same base-point component, without a regular-value premise. -/
noncomputable section
open Set Topology
namespace Yau.NodeProofs.F01Aux
variable {A : Type*} [TopologicalSpace A]

theorem conformalProfile_compact_component_sublevel
    (u : A → ℝ) (hu : Continuous u) (hproper : ∀ c : ℝ, IsCompact {x | u x ≤ c})
    (o : A) {L : ℝ} (hL : 0 < L) (B : ℝ) :
    IsCompact {x : sublevelComponent u o L | conformalProfile (u x.val / L) ≤ B} := by
  let S := sublevelComponent u o L
  let δ := min (1 / 4 : ℝ) (Real.exp (-B / 2))
  have hδ : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
  let c := L * (1 - δ)
  let K := {x : A | u x ≤ c}
  have hKU : K ⊆ u ⁻¹' Iio L := by
    intro x hx
    change u x ≤ c at hx
    have hc : c < L := by
      change L * (1 - δ) < L
      nlinarith [mul_pos hL hδ]
    exact hx.trans_lt hc
  have hcomp : IsCompact (S ∩ K) := isCompact_connectedComponentIn_inter o (hproper c) hKU
  let E := {x : S | u x.val ≤ c}
  have hE : IsCompact E := by
    apply IsInducing.subtypeVal.isCompact_iff.mpr
    convert! hcomp using 1
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hlevel (x : S) : u x.val / L < 1 :=
    (div_lt_one hL).mpr (sublevelComponent_subset u o L x.property)
  have hf : Continuous (fun x : S => conformalProfile (u x.val / L)) :=
    conformalProfile_contDiffOn.continuousOn.comp_continuous
      ((hu.comp continuous_subtype_val).div_const L) (fun x => hlevel x)
  apply hE.of_isClosed_subset (isClosed_Iic.preimage hf)
  intro x hx
  have hgap := conformalProfile_level_gap (hlevel x) hx
  change u x.val ≤ L * (1 - δ)
  have hh := mul_le_mul_of_nonneg_left hgap hL.le
  have hcancel := div_mul_cancel₀ (u x.val) hL.ne'
  dsimp only [δ] at *
  nlinarith

end Yau.NodeProofs.F01Aux
