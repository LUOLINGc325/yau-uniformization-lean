import Yau.Proofs.F05BootstrapNative
import Yau.Proofs.F05ReflectionJets

/-! Relative spatial jets on the genuine closed half-space give an actual
ambient C2 reflection. The reflected function is used for calculus and lower
jet estimates; no equation is asserted on the reflected side. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_jets_of_mem_nhds {X : Set (Space n)} {I : Set ℝ}
    {v : Point n → ℝ} (hv : F05RelC2 X I v) {z : Point n}
    (hz : z ∈ X ×ˢ I) (hX : X ∈ 𝓝 z.1) :
    HasFDerivAt (fun x => v (x,z.2)) (F05RelD X v z) z.1 ∧
      HasFDerivAt (fun x => F05RelD X v (x,z.2)) (F05RelDD X v z) z.1 := by
  have hc : ContDiffAt ℝ 2 (fun x => v (x,z.2)) z.1 :=
    (hv.2.2.2.2.1 z.2 hz.2 z.1 hz.1).contDiffAt hX
  have hFirst : (fun x => F05RelD X v (x,z.2)) =ᶠ[𝓝 z.1]
      (fun x => fderiv ℝ (fun y => v (y,z.2)) x) := by
    have hInterior : z.1 ∈ interior X := mem_interior_iff_mem_nhds.mpr hX
    filter_upwards [isOpen_interior.mem_nhds hInterior] with x hx
    exact fderivWithin_of_mem_nhds
      (mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset)
  refine ⟨?_,?_⟩
  · rw [F05RelD,fderivWithin_of_mem_nhds hX]
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt
  · rw [F05RelDD,fderivWithin_of_mem_nhds hX]
    exact (((hc.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).congr_of_eventuallyEq hFirst).hasFDerivAt

theorem F05_relative_halfSpace_reflection {e : Space n} (he : ‖e‖ = 1)
    {α T K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hK : 0 ≤ K)
    {v : Point n → ℝ}
    (hv : F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) v)
    (hBound : ∀ z ∈ {x | 0 ≤ inner ℝ e x} ×ˢ Icc 0 T,
      |v z| ≤ K ∧ ‖F05RelD {x | 0 ≤ inner ℝ e x} v z‖ ≤ K ∧
      ‖F05RelDD {x | 0 ≤ inner ℝ e x} v z‖ ≤ K ∧
      |F05RelT (Icc 0 T) v z| ≤ K) :
    let U := halfSpaceSecondOrderExtension e v
    C2 (cylinder univ 0 T) U ∧
      EqOn U v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialD U) (F05RelD {x | 0 ≤ inner ℝ e x} v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialDD U) (F05RelDD {x | 0 ≤ inner ℝ e x} v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) U) (F05RelT (Icc 0 T) v)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      (∀ z ∈ cylinder univ 0 T,
        |U z| ≤ 500*K ∧ ‖spatialD U z‖ ≤ 500*K ∧
          ‖spatialDD U z‖ ≤ 500*K ∧ |timeD (cylinder univ 0 T) U z| ≤ 500*K) ∧
      HolderBound α (cylinder univ 0 T) (fun z => (U z,spatialD U z)) (8000*K) := by
  have hOpen : IsOpen {x : Space n | 0 < inner ℝ e x} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hJets (z : Point n) (hz : z ∈ cylinder {x | 0 < inner ℝ e x} 0 T) :=
    F05_relative_jets_of_mem_nhds hv ⟨(show 0 < inner ℝ e z.1 from hz.1).le,hz.2⟩
      (mem_of_superset (hOpen.mem_nhds hz.1)
        (fun x hx => (show 0 < inner ℝ e x from hx).le))
  exact F05_reflection_jet_bounds he hα hα1 hT hK v
    (F05RelD {x | 0 ≤ inner ℝ e x} v)
    (F05RelDD {x | 0 ≤ inner ℝ e x} v) (F05RelT (Icc 0 T) v)
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    (fun z hz => (hJets z hz).1) (fun z hz => (hJets z hz).2)
    (fun z hz => (hv.2.2.2.2.2 z hz).hasDerivWithinAt) hBound

end Yau.Proofs.F05Aux
