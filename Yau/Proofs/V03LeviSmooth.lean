import Yau.Proofs.V03LeviChain

/-! Smoothness of the actual diagonal real Levi value as a function of
the point and tangent direction. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def realLeviValue (f : E → ℝ) (z v : E) : ℝ :=
  (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re

theorem realLeviValue_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun p : E × E => realLeviValue f p.1 p.2) (U ×ˢ Set.univ) := by
  have hH := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU
    (m := ∞) (by simp)
  have hcomp : ContDiffOn ℝ ∞ (fun p : E × E => fderiv ℝ (fderiv ℝ f) p.1)
      (U ×ˢ Set.univ) :=
    hH.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hI : ContDiffOn ℝ ∞ (fun p : E × E => Complex.I • p.2) (U ×ˢ Set.univ) :=
    contDiffOn_const.smul contDiffOn_snd
  have hfirst := (hcomp.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd
  have hsecond := (hcomp.clm_apply hI).clm_apply hI
  apply (contDiffOn_const.mul (hfirst.add hsecond)).congr
  intro p hp
  exact mixedWirt_real_diagonal ((hf.contDiffAt (hU.mem_nhds hp.1)).of_le (by simp)) p.2

end Yau.Blueprint.V03Proof
