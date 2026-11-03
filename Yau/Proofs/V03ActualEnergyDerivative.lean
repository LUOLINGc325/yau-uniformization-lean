import Yau.Proofs.V03ActualBaseGaussEnergyDerivative
import Yau.Proofs.V03ActualEnergyMixedSplit
import Yau.Proofs.V03ActualLogEnergyDerivative

/-! The full original actual mixed energy derivative estimate, including
the unchanged logarithmic wall energy and one constant before every realization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem actualEnergyDerivative {n q : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) : ActualEnergyDerivative d j a := by
  intro L hL
  obtain ⟨Cb, hCb, hb⟩ := actualBaseAreaEnergyDerivative hd j a L hL
  obtain ⟨Ce, hCe, he⟩ := actualEuclideanEnergyDerivative hd j a L hL
  obtain ⟨Cg, hCg, hg⟩ := actualGaussAreaEnergyDerivative hd j a L hL
  obtain ⟨Cl, hCl, hl⟩ := actualLogEnergyDerivative hd j a ha L hL
  refine ⟨Cb + Ce + Cg + Cl, by positivity,
    fun F E l h α fz R hF hE hcol hlL hR => ?_⟩
  change |mixedReal (fun z => (variationEnergy d j {F with f := fz z}).toReal)| ≤ _
  rw [realized_energy_mixed_split hd hR]
  have h₁ := hb F E l h α fz R hF hE hcol hlL hR
  have h₂ := he F E l h α fz R hF hE hcol hlL hR
  have h₃ := hg F E l h α fz R hF hE hcol hlL hR
  have h₄ := hl F E l h α fz R hF hE hcol hlL hR
  calc
    _ ≤ |mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal) +
        mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal) +
          mixedReal (fun z => gaussArea d.G (fz z))| +
            |mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal)| := abs_add_le _ _
    _ ≤ |mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal) +
        mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal)| +
          |mixedReal (fun z => gaussArea d.G (fz z))| +
            |mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal)| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal)| +
        |mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal)| +
          |mixedReal (fun z => gaussArea d.G (fz z))| +
            |mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal)| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ _ := by nlinarith

end Yau.Blueprint.V03Proof
