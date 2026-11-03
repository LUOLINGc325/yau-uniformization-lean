import Yau.Proofs.V04NegativeFamily
import Yau.Proofs.V04UniformCenters

/-! The original negative-part component follows from the original V04
analytic inputs. Compact centers, Fejer constants, and deformation
constants precede the family; the sequence limit remains inside epsilon. -/

open Filter
open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem negativePartEstimates_of_original_inputs {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (ha : 4 ≤ a)
    (hloc : LocalizationEstimates d) (hsymbol : SymbolBounds d a)
    (hdeform : ∀ᶠ j in atTop, DeformationEstimate d j a) : NegativePartEstimates d a := by
  obtain ⟨Kc, hKc, hKint, hcenters⟩ := uniform_minimizing_centers hd hloc
  have hFejer := fejerEstimates_of_symbolBounds hd ha hsymbol
  filter_upwards [hcenters, hdeform] with j hj hdef
  obtain ⟨C, hC, hfejer⟩ := hFejer j
  obtain ⟨M, hM, hsymj⟩ := hsymbol j
  obtain ⟨CE, hCE, hCEdef⟩ := hdef C hC
  have hdefWith : DeformationEstimateWith d j a C CE := hCEdef d.test hd.2.2.2.2.2.2.2.1
  intro F E hdata hzero
  obtain ⟨B, P, hBlim, hfreq, hupper⟩ := negative_family_upper hd ha hC hCE hM hdefWith
    hfejer (fun F E hF hE => (hsymj F E hF hE).1) Kc hKc hKint hj F E hdata hzero
  have hR := negativeFamilyError_tendsto ((2 * n : ℕ) * CE) C
    (2 * (((2 * n : ℕ) : ℝ) * M) ^ 2) B P hBlim hfreq
  have hthree := epsSeqZero_of_nonneg_upper
    (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 3)
    (negativeFamilyError ((2 * n : ℕ) * CE) C (2 * (((2 * n : ℕ) : ℝ) * M) ^ 2) B P)
    (fun ε ν => negativeTrace_nonneg _ _ _ _ 3) hR hupper
  refine ⟨hthree, negativeTrace_one_of_three hd ha hsymbol j F E ?_ hthree⟩
  filter_upwards [hdata] with ε hε
  intro ν
  exact ⟨hε.1.1 ν, hε.2 ν⟩

end Yau.Blueprint.V04Proof
