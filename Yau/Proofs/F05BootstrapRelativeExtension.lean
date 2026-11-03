import Yau.Proofs.F05BootstrapReflection

/-! Qualitative reflection needs continuity of the genuine one-sided jets,
with no global bound on those jets. The operator identity is asserted only
on the original closed half-space. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_halfSpace_extension {e : Space n} (he : ‖e‖ = 1) {T : ℝ}
    (hT : 0 < T) {v : Point n → ℝ}
    (hv : F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) v) :
    let U := halfSpaceSecondOrderExtension e v
    C2 (cylinder univ 0 T) U ∧
      EqOn U v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialD U) (F05RelD {x | 0 ≤ inner ℝ e x} v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialDD U) (F05RelDD {x | 0 ≤ inner ℝ e x} v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) U) (F05RelT (Icc 0 T) v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  have hOpen : IsOpen {x : Space n | 0 < inner ℝ e x} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hJets (z : Point n) (hz : z ∈ cylinder {x | 0 < inner ℝ e x} 0 T) :=
    F05_relative_jets_of_mem_nhds hv ⟨(show 0 < inner ℝ e z.1 from hz.1).le,hz.2⟩
      (mem_of_superset (hOpen.mem_nhds hz.1)
        (fun x hx => (show 0 < inner ℝ e x from hx).le))
  exact halfSpaceSecondOrderExtension_jets he hT v
    (F05RelD {x | 0 ≤ inner ℝ e x} v)
    (F05RelDD {x | 0 ≤ inner ℝ e x} v) (F05RelT (Icc 0 T) v)
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    (fun z hz => (hJets z hz).1) (fun z hz => (hJets z hz).2)
    (fun z hz => (hv.2.2.2.2.2 z hz).hasDerivWithinAt)

theorem F05_relative_extension_operator {e : Space n} (he : ‖e‖ = 1) {T : ℝ}
    (hT : 0 < T) {v : Point n → ℝ}
    (hv : F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) v)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {z : Point n} (hz : z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b
      (halfSpaceSecondOrderExtension e v) z =
    F05RelOp {x | 0 ≤ inner ℝ e x} (Icc 0 T) a b v z := by
  obtain ⟨hU,hValue,hD,hDD,hTime⟩ := F05_relative_halfSpace_extension he hT hv
  unfold linearOp F05RelOp
  rw [timeD_cylinder_restrict_space _ hz,hTime hz,hD hz,hDD hz]

end Yau.Proofs.F05Aux
