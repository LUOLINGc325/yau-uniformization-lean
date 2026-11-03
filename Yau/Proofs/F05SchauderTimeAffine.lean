import Yau.Proofs.F05SchauderLinear

/-! A uniform, explicit Schauder budget for affine changes of time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_schauder_timeAffine {X : Set (Space n)} {l r L R α C a b : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => a*t+b) (Icc l r) (Icc L R))
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder X L R) u C) :
    SchauderBound α (cylinder X l r) (F05TimeAffine a b u)
      (C*((1+|a|)*(1+|a|^(α/2)))) := by
  have ha := abs_nonneg a
  have hPow := Real.rpow_nonneg (abs_nonneg a) (α/2)
  have hC := hu.2.1
  have hCa := mul_nonneg hC ha
  have hCp := mul_nonneg hC hPow
  have hCap := mul_nonneg hCa hPow
  have hBase : C ≤ C*((1+|a|)*(1+|a|^(α/2))) := by nlinarith
  have hHigh : C*(1+|a|^(α/2)) ≤ C*((1+|a|)*(1+|a|^(α/2))) := by nlinarith
  have hTimeBudget : |a| * (C*(1+|a|^(α/2))) ≤ C*((1+|a|)*(1+|a|^(α/2))) := by nlinarith
  refine ⟨F05_c2_timeAffine hlr hMap hu.1,by positivity,?_,?_,?_⟩
  · intro p hp
    exact ⟨((hu.2.2.1 (F05TimeAffinePoint a b p) ⟨hp.1,hMap hp.2⟩).1).trans hBase,
      ((hu.2.2.1 (F05TimeAffinePoint a b p) ⟨hp.1,hMap hp.2⟩).2).trans hBase⟩
  · exact holderBound_mono_const (F05_holder_timeAffine hMap hu.2.2.2.1) hHigh
  · apply holderBound_congr_on
      (holderBound_mono_const (F05_holder_const_smul (F05_holder_timeAffine hMap hu.2.2.2.2) a) hTimeBudget)
    intro p hp
    exact (F05_timeD_timeAffine hlr hMap hu.1 hp).symm

end Yau.Proofs.F05Aux
