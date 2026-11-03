import Yau.Proofs.C01PathEnergyTimeJets
import Yau.Proofs.C01EnergyUpperSupport
import Yau.Proofs.C01ExitSphere

/-! A genuine constant-speed minimizing boundary path gives an actual
energy upper support for the first-exit profile at all nonnegative times. -/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_path_energy_upper_support
    (hflow : LocalizedFlow X o h U P ρ) (L a : ℝ) (hL : 0 < L) (ha : 0 < a)
    (β : ℝ → Pt X) :
    letI := manifold_realSmooth X.manifold
    ∀ hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 β,
    β 0 = o → β 1 ∈ initialDistanceSphere X.metric o L →
    (∀ u ∈ Set.Icc (0 : ℝ) 1,
      realTangentSpeedSq (h a) (β u) (realCurveVelocity β u) =
        exitDistanceProfile X.metric (h a) o L ^ 2) →
    ∃ f : ℝ → ℝ,
      f a = exitDistanceProfile X.metric (h a) o L ∧
      (∀ t, 0 ≤ t → exitDistanceProfile X.metric (h t) o L ≤ f t) ∧
      HasDerivAt f
        (-(∫ u in Set.Icc (0 : ℝ) 1,
          actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u)) /
          (2 * exitDistanceProfile X.metric (h a) o L)) a := by
  letI := manifold_realSmooth X.manifold
  intro hf hf₀ hboundary hspeed
  let l : ℝ → ℝ := fun t => exitDistanceProfile X.metric (h t) o L
  let E : ℝ → ℝ := fun t => actualPathEnergy (h t) β
  have hd : 0 < l a := exitDistanceProfile_pos X.metric (h a)
    (localizedFlow_metricSmooth_nonneg hflow a ha.le) o L hL
  have hEa : E a = l a ^ 2 := actualPathEnergy_eq_of_constant_speedSq (h a) β (l a ^ 2) hspeed
  have hupper (t : ℝ) (ht : t ∈ Set.Ici 0) : l t ^ 2 ≤ E t := by
    have hk := localizedFlow_metricSmooth_nonneg hflow t ht
    have hmin := exitDistanceProfile_le X.metric (h t) hk o L hL.le (β 1) hboundary
    have hminnonneg : 0 ≤ l t := (exitDistanceProfile_pos X.metric (h t) hk o L hL).le
    have hdnonneg := inducedDistance_nonneg (h t) hk o (β 1)
    have hsq := (sq_le_sq₀ hminnonneg hdnonneg).mpr hmin
    have HE := distance_sq_le_actualPathEnergy (h t) hk β (hf.of_le (by norm_num))
    rw [hf₀] at HE
    exact hsq.trans HE
  have hE := localizedFlow_actualPathEnergy_hasDerivAt hflow β Set.univ isOpen_univ
    (Set.subset_univ _) hf.contMDiffOn a ha
  obtain ⟨htouch, hbound, hderiv⟩ := energy_sqrt_upperTouch l E (Set.Ici 0) a (l a)
    (∫ u in Set.Icc (0 : ℝ) 1, actualRealRicciQuadratic (h a) (β u) (realCurveVelocity β u))
    hd rfl hEa hupper hE
  exact ⟨fun t => Real.sqrt (E t), htouch, hbound, hderiv⟩

end Yau.NodeProofs.C01Aux
