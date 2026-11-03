import Yau.Proofs.V04SpectralFactorEstimates
import Yau.Proofs.V04CenterMajorants

/-! The original center-majorant component now uses only the original
V04 analytic inputs. Its factor-estimate premise is supplied internally
for the same symbol and every caller-supplied factor. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem centerMajorants_of_symbolBounds {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (ha : 4 ≤ a)
    (hloc : LocalizationEstimates d) (hsymbol : SymbolBounds d a)
    (hdeform : ∀ᶠ j in atTop, DeformationEstimate d j a) : CenterMajorants d a :=
  centerMajorants_of_original_components hd ha hloc hsymbol
    (spectralFactorEstimates_of_symbolBounds hd ha hsymbol) hdeform

end Yau.Blueprint.V04Proof
