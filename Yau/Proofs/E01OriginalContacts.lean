import Yau.Proofs.E01John
import Yau.Proofs.E01EnvelopeScale
import Yau.Proofs.E01EnvelopeTopology

/-! The exact finite contacts and small coefficients in the original E01 coordinates. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem original_max_small_contacts (h : Flow X) (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Set.Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x z t B)
    (hmax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ envelopeChart h T x (z, η i, t) = 1 ∧
        (star (WithLp.ofLp (η i)) ⬝ᵥ (B *ᵥ WithLp.ofLp (η i))).re = 1) ∧
      (∑ i, (α i : ℂ) • Matrix.vecMulVec (WithLp.ofLp (η i)) (star (WithLp.ofLp (η i)))) = B⁻¹ ∧
      ∑ i, α i = n := by
  have hh := small_contacts_of_positive_max (fun η => envelopeChart h T x (z, η, t))
    (envelopeChart_fiber_lowerSemicontinuous h T x z t hz ht)
    (fun r hr η => envelopeChart_positive_real_smul h T x z η t hz ht r hr)
    B hB.1 hB.2 (fun D hD hDv => hmax D ⟨hD, hDv⟩) ε hε
  simpa only [ellipsoidQuadratic, contactRankOne] using hh

end Yau.NodeProofs.E01Aux
