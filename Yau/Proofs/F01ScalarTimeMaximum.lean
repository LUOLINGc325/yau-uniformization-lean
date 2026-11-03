import Yau.Proofs.F01ClosedScalarTimeHeat
import Yau.Proofs.F01ClosedScalarHeat
import Yau.Proofs.F01BoundedMaximum
import Yau.Proofs.F01ClosedTimeBounds

/-! The actual bounded maximum principle applied to the actual scalar
time jet gives the original linear and quadratic upper potential estimates.
The boundedness premise is an ordinary scalar bound to be supplied by the
uniform chart estimates, not a new solver or final theorem hypothesis. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem fieldHeatWithin_sub_const (h : ℝ → HermitianField M)
    {F : M.Carrier → ℝ → ℝ} {I : Set ℝ} (hF : SmoothSpaceTime F I)
    (c : ℝ) (x : M.Carrier) {t : ℝ} (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t) :
    fieldHeatWithin h I (fun s y => F y s - c) x t =
      fieldHeatWithin h I (fun s y => F y s) x t := by
  have hc : SmoothFn (fun _ : M.Carrier => c) := fun _ => contDiffOn_const
  have hh := fieldHeatWithin_sub_space_time_penalty h hF hc 1 0 x ht hI
  simpa only [one_mul, zero_mul, sub_zero, laplacian_const_native, add_zero] using hh

theorem bounded_scalar_time_jet_upper
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T a Bpt : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hh0 : h 0 = α)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hinit : ∀ x, -scalarCurvature α x ≤ a)
    (hbound : ∀ x t, t ∈ Icc 0 T → flowLogDetTime α h (Icc 0 T) x t ≤ Bpt)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b}) {B : ℝ}
    (hlap : ∀ x t, t ∈ Icc 0 T → laplacian (h t) f x ≤ B) :
    ∀ x t, t ∈ Icc 0 T → flowLogDetTime α h (Icc 0 T) x t ≤ a := by
  have hPt := flowLogDetTime_smoothSpaceTime α hα h (uniqueDiffOn_Icc hT) hh
  have hvalue (x : M.Carrier) : flowLogDetTime α h (Icc 0 T) x 0 = -scalarCurvature α x := by
    have hd := (closed_slab_logdet_evolution_and_heat α hα h U hT hh hU hpot hpde
      x ⟨le_refl 0, hT.le⟩).1
    have hv := hd.derivWithin ((uniqueDiffOn_Icc hT) 0 ⟨le_refl 0, hT.le⟩)
    simpa only [flowLogDetTime, hh0] using hv
  have hmax := bounded_subcaloric_nonpos h
    (fun x t => flowLogDetTime α h (Icc 0 T) x t - a) hT
    (fun x => (hPt x).sub contDiffOn_const)
    (fun x => by rw [hvalue x]; exact sub_nonpos.mpr (hinit x))
    (fun x t ht => sub_le_sub_right (hbound x t ht) a) f hf hf0 hproper hlap
    (fun x t ht => by
      rw [fieldHeatWithin_sub_const h hPt a x ⟨ht.1.le, ht.2⟩
        ((uniqueDiffOn_Icc hT) t ⟨ht.1.le, ht.2⟩)]
      exact closed_slab_scalar_time_heat_nonpos α hα h U hT hh hU hpot hpde x t ⟨ht.1.le, ht.2⟩)
  exact fun x t ht => sub_nonpos.mp (hmax x t ht)

end Yau.NodeProofs.F01Aux
