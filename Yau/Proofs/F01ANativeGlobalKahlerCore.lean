import Yau.Proofs.F01AKahlerPotentialClosure
import Yau.Proofs.F01ClosedScalarHeat
import Yau.Proofs.F01LogDetRatioSmooth

/-! Assembly of the first eleven actual localized-flow conjuncts from
one native global potential. The scalar sign is supplied by its actual
logdet time jet and is identified with minus the computed scalar curvature. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem hasDerivWithinAt_Ici_of_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {d : F} {t T : ℝ}
    (ht : 0 ≤ t) (hT : t < T)
    (hf : HasDerivWithinAt f d (Icc 0 T) t) :
    HasDerivWithinAt f d (Ici 0) t := by
  apply hf.mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hT))

theorem global_potential_metric_evolution
    (g : HermitianField M) (hg : MetricSmooth g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (hh : MetricFamilySmooth h (Ici 0)) (hU : SmoothSpaceTime U (Ici 0))
    (hpot : ∀ s, 0 ≤ s → ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, 0 ≤ s → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Ici 0) s) :
    ∀ x t, 0 ≤ t → ∀ i j : Fin n,
      HasDerivWithinAt (fun s => gMat (h s) x i j)
        (-ricci (h t) x i j) (Ici 0) t := by
  intro x t ht i j
  let T := t + 1
  have hT : 0 < T := by dsimp only [T]; linarith
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun s hs => hs.1
  have hmetric := closed_slab_potential_metric_evolution g hg h U hT
    (fun x a b => (hh x a b).mono (prod_mono Subset.rfl hsub))
    (fun x => (hU x).mono (prod_mono Subset.rfl hsub))
    (fun s hs => hpot s hs.1) (fun x s hs => (hpde x s hs.1).mono hsub)
    x i j t ⟨ht, by dsimp only [T]; linarith⟩
  exact hasDerivWithinAt_Ici_of_Icc ht (by dsimp only [T]; linarith) hmetric

/-- The literal first eleven conjuncts of `LocalizedFlow`. -/
def LocalizedFlowCore (X : KahlerManifold n)
    (h : Flow X) (U P ρ : STF X) : Prop :=
  IsKahlerRicciFlow X.metric.form h ∧
  SmoothSpaceTime U (Ici 0) ∧ SmoothSpaceTime P (Ici 0) ∧ SmoothSpaceTime ρ (Ici 0) ∧
  (∀ t, 0 ≤ t → ∀ x, HermLE (gMat (h t) x) (gMat X.metric.form x)) ∧
  (∀ t, 0 ≤ t → ∀ x, gMat (h t) x = gMat X.metric.form x -
    (t : ℂ) • ricci X.metric.form x + levi (fun y => U y t) x) ∧
  (∀ x, U x 0 = 0) ∧
  (∀ x t, 0 ≤ t → HasDerivWithinAt (U x) (P x t) (Ici 0) t) ∧
  (∀ x t, 0 ≤ t → P x t = Real.log
    ((gMat (h t) x).det.re / (gMat X.metric.form x).det.re)) ∧
  (∀ x t, 0 ≤ t → ρ x t = -P x t ∧ 0 ≤ ρ x t) ∧
  (∀ x t, 0 ≤ t → HasDerivWithinAt (P x) (-scalarCurvature (h t) x) (Ici 0) t ∧
    0 ≤ scalarCurvature (h t) x)

theorem native_global_core_of_actual_potential
    (X : KahlerManifold n) (h : Flow X) (U : STF X)
    (hh0 : h 0 = X.metric.form)
    (hh : MetricFamilySmooth h (Ici 0)) (hU : SmoothSpaceTime U (Ici 0))
    (hupper : ∀ t, 0 ≤ t → ∀ x, HermLE (gMat (h t) x) (gMat X.metric.form x))
    (hpot : ∀ t, 0 ≤ t → ∀ x, gMat (h t) x = gMat X.metric.form x -
      (t : ℂ) • ricci X.metric.form x + levi (fun y => U y t) x)
    (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x t, 0 ≤ t → HasDerivWithinAt (U x)
      (flowLogDetRatio X.metric.form h x t) (Ici 0) t)
    (hPnonpos : ∀ x t, 0 ≤ t → flowLogDetRatio X.metric.form h x t ≤ 0)
    (hPt : ∀ x t, 0 ≤ t →
      derivWithin (flowLogDetRatio X.metric.form h x) (Ici 0) t ≤ 0) :
    LocalizedFlowCore X h U (flowLogDetRatio X.metric.form h)
      (fun x t => -flowLogDetRatio X.metric.form h x t) := by
  have hg : MetricSmooth X.metric.form :=
    Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hevol := global_potential_metric_evolution X.metric.form hg h U hh hU hpot hpde
  have hP := flowLogDetRatio_smoothSpaceTime X.metric.form hg h hh
  refine ⟨⟨hh0, hh, ?_, hevol⟩, hU, hP,
    (fun x => (hP x).neg), hupper, hpot, hU0, hpde,
    (fun _ _ _ => rfl), (fun x t ht => ⟨rfl, neg_nonneg.mpr (hPnonpos x t ht)⟩), ?_⟩
  · intro t ht
    exact kahlerClosed_of_native_potential X.metric.form (h t) hg X.kahler_metric
      (fun y => U y t) (smoothSpaceTime_slice hU ht) t (hpot t ht)
  · intro x t ht
    have hd := native_logdet_ratio_hasDerivWithinAt X.metric.form h x (hevol x t ht)
    refine ⟨hd, ?_⟩
    have hv := hPt x t ht
    rw [hd.derivWithin ((uniqueDiffOn_Ici 0) t ht)] at hv
    linarith

end Yau.NodeProofs.F01Aux
