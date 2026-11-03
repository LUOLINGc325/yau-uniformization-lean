import Yau.Proofs.F01AAmbientApproximationSequence
import Yau.Proofs.F01AControlledScalarCaps
import Yau.Proofs.F01AActualTimeIdentification
import Yau.Proofs.F01PotentialMetricAssembly

/-! Actual point data for the one continued approximating family. The
finite scalar caps are transported to any fixed closed integer horizon
using their genuine derivative witnesses, including both time faces. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The actual extended potential and actual extended logdet satisfy all
finite point equations and caps on every fixed closed integer horizon. -/
theorem actual_approximation_closed_point_data
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (V : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (V m)) :
    let f : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m) (V m)
    let p : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m)
      (flowLogDetRatio (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m))
    ∃ a0 : ℝ, 0 < a0 ∧ ∀ x (k : ℕ), ∀ᶠ m in atTop, ∀ t ∈ Icc 0 ((k : ℝ) + 1),
      HasDerivWithinAt (f m x) (p m x t) (Icc 0 ((k : ℝ) + 1)) t ∧
      p m x t = Real.log ((nativePotentialMatrix X.metric.form (f m) t x).det.re /
        (gMat X.metric.form x).det.re) ∧
      p m x t ≤ (a0 * t) / L m ^ 2 ∧
      derivWithin (fun s => derivWithin (f m x) (Icc 0 ((k : ℝ) + 1)) s)
        (Icc 0 ((k : ℝ) + 1)) t ≤ a0 / L m ^ 2 := by
  let f : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m) (V m)
  let p : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m)
    (flowLogDetRatio (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m))
  obtain ⟨a0, ha0, hcaps⟩ := controlled_native_scalar_caps X o u hu
  refine ⟨a0, ha0, ?_⟩
  intro x k
  obtain ⟨Lc, _, hcore⟩ := compact_approximation_identity X o u hu
    (isCompact_singleton : IsCompact ({x} : Set (Pt X)))
  filter_upwards [hL.eventually (eventually_ge_atTop Lc), eventually_ge_atTop k] with m hm hmK
  let Nm := sublevelManifold X.manifold u hu.1 o (L m) (ho m)
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)
  let H := (k : ℝ) + 1
  let T := (m : ℝ) + 2
  let xm : Nm.Carrier := ⟨x, (hcore (L m) hm (ho m)).1 (mem_singleton x)⟩
  have hH : 0 < H := by dsimp only [H]; positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  have hHT : H ≤ T := by
    have hcast : (k : ℝ) ≤ m := by exact_mod_cast hmK
    dsimp only [H, T]
    linarith
  have hsub : Icc (0 : ℝ) H ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans hHT⟩
  have hf : f m x = V m xm := by
    funext s
    exact openExtendedPotential_restrict X.manifold (sublevelOpens X.manifold u hu.1 o (L m))
      (sublevelComponent_isConnected (ho m)) (V m) xm s
  have hp : p m x = flowLogDetRatio α (h m) xm := by
    funext s
    exact openExtendedPotential_restrict X.manifold (sublevelOpens X.manifold u hu.1 o (L m))
      (sublevelComponent_isConnected (ho m)) (flowLogDetRatio α (h m)) xm s
  obtain ⟨hh0, hh, hV, hV0, C, hC, hdata⟩ := hsol m
  have hpde : ∀ s ∈ Icc 0 H, HasDerivWithinAt (f m x) (p m x s) (Icc 0 H) s := by
    intro s hs
    rw [hf, hp]
    exact ((hdata xm s (hsub hs)).2.2.2).mono hsub
  have hbackground := (hcore (L m) hm (ho m)).2 xm (mem_singleton x)
  have hα : MetricSmooth α := approximatingMetric_metricSmooth X.manifold
    (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) hu.1 o
    ((zero_lt_one.trans_le (hu.2.2.1 o)).trans (ho m)) (ho m)
  intro t ht
  have htH : t ∈ Icc 0 H := ht
  have htT : t ∈ Icc 0 T := hsub htH
  have hmatrix : gMat (h m t) xm = nativePotentialMatrix X.metric.form (f m) t x := by
    have hlevi : levi (fun y => f m y t) x = levi (fun y => V m y t) xm :=
      openExtendedPotential_levi X.manifold (sublevelOpens X.manifold u hu.1 o (L m))
        (sublevelComponent_isConnected (ho m)) (V m) xm t
    rw [(hdata xm t htT).2.2.1, hbackground.2.1, hbackground.2.2]
    change gMat X.metric.form x - (t : ℂ) • ricci X.metric.form x +
      levi (fun y => V m y t) xm = gMat X.metric.form x -
        (t : ℂ) • ricci X.metric.form x + levi (fun y => f m y t) x
    rw [hlevi]
  have hlog : p m x t = Real.log ((nativePotentialMatrix X.metric.form (f m) t x).det.re /
      (gMat X.metric.form x).det.re) := by
    rw [hp]
    change Real.log ((gMat (h m t) xm).det.re / (gMat α xm).det.re) = _
    rw [hbackground.2.1, hmatrix]
  have hc := hcaps (L m) (ho m) T (h m) (V m) hT (hsol m) xm t htT
  have hpcap : p m x t ≤ (a0 * t) / L m ^ 2 := by
    rw [hp]
    calc
      _ ≤ (a0 / L m ^ 2) * t := hc.2.1
      _ = _ := by ring
  have hd := (closed_slab_logdet_evolution_and_heat α hα (h m) (V m) hT hh hV
    (fun s hs y => (hdata y s hs).2.2.1) (fun y s hs => (hdata y s hs).2.2.2) xm htT).1
  have hdcap : -scalarCurvature (h m t) xm ≤ a0 / L m ^ 2 := by
    have hcap := hc.1
    change derivWithin (flowLogDetRatio α (h m) xm) (Icc 0 T) t ≤ _ at hcap
    rw [hd.derivWithin ((uniqueDiffOn_Icc hT) t htT)] at hcap
    exact hcap
  have hsecond : derivWithin (fun s => derivWithin (f m x) (Icc 0 H) s) (Icc 0 H) t ≤
      a0 / L m ^ 2 := by
    rw [actual_second_clock_eq_derivWithin_of_pde (f m x) (p m x) hH htH hpde, hp,
      (hd.mono hsub).derivWithin ((uniqueDiffOn_Icc hH) t htH)]
    exact hdcap
  exact ⟨hpde t htH, hlog, hpcap, hsecond⟩

/-- The exact four finite-data inputs of the actual native-core assembly,
before any subsequence is chosen. All data are produced from the fixed
actual family, with a single scalar coefficient preceding x and k. -/
theorem actual_approximation_point_data
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (V : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (V m)) :
    let f : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m) (V m)
    let p : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m)
      (flowLogDetRatio (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m))
    ∃ a0 : ℝ, 0 < a0 ∧
      (∀ x (k : ℕ), ∀ᶠ m in atTop, ∀ t ∈ Icc 0 ((k : ℝ) + 1),
        HasDerivWithinAt (f m x) (p m x t) (Icc 0 ((k : ℝ) + 1)) t) ∧
      (∀ x t, 0 ≤ t → ∀ᶠ m in atTop,
        p m x t = Real.log ((nativePotentialMatrix X.metric.form (f m) t x).det.re /
          (gMat X.metric.form x).det.re)) ∧
      (∀ x t, 0 ≤ t → ∀ᶠ m in atTop, p m x t ≤ (a0 * t) / L m ^ 2) ∧
      (∀ x (k : ℕ), ∀ᶠ m in atTop, ∀ t ∈ Icc 0 ((k : ℝ) + 1),
        derivWithin (fun s => derivWithin (f m x) (Icc 0 ((k : ℝ) + 1)) s)
          (Icc 0 ((k : ℝ) + 1)) t ≤ a0 / L m ^ 2) := by
  obtain ⟨a0, ha0, hpoint⟩ := actual_approximation_closed_point_data X o u hu L ho h V hL hsol
  refine ⟨a0, ha0, ?_, ?_, ?_, ?_⟩
  · intro x k
    exact (hpoint x k).mono (fun m hm t ht => (hm t ht).1)
  · intro x t ht
    obtain ⟨k, hk⟩ := exists_nat_gt t
    have htk : t ∈ Icc 0 ((k : ℝ) + 1) := ⟨ht, by linarith⟩
    exact (hpoint x k).mono (fun m hm => (hm t htk).2.1)
  · intro x t ht
    obtain ⟨k, hk⟩ := exists_nat_gt t
    have htk : t ∈ Icc 0 ((k : ℝ) + 1) := ⟨ht, by linarith⟩
    exact (hpoint x k).mono (fun m hm => (hm t htk).2.2.1)
  · intro x k
    exact (hpoint x k).mono (fun m hm t ht => (hm t ht).2.2.2)

end Yau.NodeProofs.F01Aux
