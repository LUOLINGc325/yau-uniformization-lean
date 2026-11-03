import Yau.Proofs.F05CanonicalLinear
import Yau.Proofs.F05CanonicalRealization

/-! The actual global realization preserves scalar vector-space operations. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05CanonicalPull_sub (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u v : F05CompatibleJetGraph A α hT) (i : Fin A.count) :
    F05CanonicalPull A χ α hT (u-v) i =
      fun p => F05CanonicalPull A χ α hT u i p-F05CanonicalPull A χ α hT v i p := by
  funext p
  simp only [F05CanonicalPull,← F05CanonicalJetLinear_apply,map_sub,Pi.sub_apply]

theorem F05CanonicalPull_zero (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (i : Fin A.count) :
    F05CanonicalPull A χ α hT 0 i = 0 := by
  funext p
  simp only [F05CanonicalPull,← F05CanonicalJetLinear_apply,map_zero,Pi.zero_apply]

end Yau.Proofs.F05Aux
