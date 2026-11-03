import Yau.Proofs.F05BootstrapDefinitions

/-! Outside the actual closed support of a spatial cutoff, every computed
relative jet of the localized field vanishes, without a regularity premise. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cutoff_zero_jets (X : Set (Space n)) (I : Set ℝ)
    (φ : Space n → ℝ) (u : Point n → ℝ) {z : Point n} (hz : z.1 ∉ tsupport φ) :
    (fun p => φ p.1*u p) z = 0 ∧
      F05RelD X (fun p => φ p.1*u p) z = 0 ∧
      F05RelDD X (fun p => φ p.1*u p) z = 0 ∧
      F05RelT I (fun p => φ p.1*u p) z = 0 := by
  have hSlice (x : Space n) (hx : x ∉ tsupport φ) :
      (fun y => φ y*u (y,z.2)) =ᶠ[𝓝 x] (fun _ : Space n => (0 : ℝ)) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    rw [hy,zero_mul]
  have hD (x : Space n) (hx : x ∉ tsupport φ) :
      F05RelD X (fun p => φ p.1*u p) (x,z.2) = 0 := by
    simpa only [F05RelD,fderivWithin_fun_const,Pi.zero_apply] using
      (hSlice x hx).fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := X)
  have hFirst : (fun x => F05RelD X (fun p => φ p.1*u p) (x,z.2)) =ᶠ[𝓝 z.1]
      (fun _ : Space n => (0 : Space n →L[ℝ] ℝ)) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with x hx
    exact hD x hx
  have hφ : φ z.1 = 0 := image_eq_zero_of_notMem_tsupport hz
  refine ⟨by change φ z.1*u z = 0; rw [hφ,zero_mul],hD z.1 hz,?_,?_⟩
  · simpa only [F05RelDD,fderivWithin_fun_const,Pi.zero_apply] using
      hFirst.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := X)
  · unfold F05RelT
    simp only [hφ,zero_mul,derivWithin_fun_const,Pi.zero_apply]

end Yau.Proofs.F05Aux
