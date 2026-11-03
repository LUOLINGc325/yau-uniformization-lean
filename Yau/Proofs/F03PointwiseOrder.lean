import Yau.LeafProofs.L18

/-! Lifting actual-volume AE identities and order to continuous interior representatives. -/

noncomputable section
open MeasureTheory Filter Set

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem eqOn_open_of_riemannian_ae_eq (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f k : M.Carrier → ℝ)
    (hf : ContinuousOn f O) (hk : ContinuousOn k O) (hfk : f =ᵐ[μ.restrict O] k) :
    EqOn f k O := by
  have : μ.IsOpenPosMeasure := riemannianVolume_isOpenPosMeasure g μ hμ
  exact Measure.eqOn_open_of_ae_eq hfk hO hf hk

theorem leOn_open_of_riemannian_ae_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f k : M.Carrier → ℝ)
    (hf : ContinuousOn f O) (hk : ContinuousOn k O)
    (hfk : ∀ᵐ x ∂μ.restrict O, f x ≤ k x) : ∀ x ∈ O, f x ≤ k x := by
  have hmin : (fun x => min (f x) (k x)) =ᵐ[μ.restrict O] f :=
    hfk.mono (fun _ hx => min_eq_left hx)
  have hmc : ContinuousOn (fun x => min (f x) (k x)) O := hf.inf hk
  have heq := eqOn_open_of_riemannian_ae_eq g μ hμ O hO _ f hmc hf hmin
  intro x hx
  exact min_eq_left_iff.mp (heq hx)

end Yau.Proofs.F03Aux
