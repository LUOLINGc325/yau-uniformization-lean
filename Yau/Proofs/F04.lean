import Yau.Blueprint.Nodes
import Yau.LeafProofs.L12

/-!
Elementary identities for the supplied localized flow in F04.

These lemmas concern the same `h`, `P`, and `ρ` supplied by the original
contract. They do not construct or substitute another flow.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

def source (X : KahlerManifold n) (h : Flow X) : STF X :=
  fun x t => traceWith (gMat (h t) x) (ricci X.metric.form x)

def density (ρ : STF X) : STF X := fun x t => Real.exp (-ρ x t)

def ZeroInitial (f : STF X) : Prop := ∀ x, f x 0 = 0

theorem potential_initial (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) : ZeroInitial P := by
  intro x
  have hp := hloc.2.2.2.2.2.2.2.2.1 x 0 le_rfl
  rw [hloc.1.1] at hp
  by_cases hd : (gMat X.metric.form x).det.re = 0
  · simpa [hd] using hp
  · simpa [hd] using hp

theorem rho_initial (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) : ZeroInitial ρ := by
  intro x
  rw [(hloc.2.2.2.2.2.2.2.2.2.1 x 0 le_rfl).1,
    potential_initial o h U P ρ hloc x, neg_zero]

theorem rho_nonneg (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ ρ x t :=
  (hloc.2.2.2.2.2.2.2.2.2.1 x t ht).2

theorem rho_hasDerivWithinAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (ρ x) (scalarCurvature (h t) x) (Set.Ici 0) t := by
  have hp : HasDerivWithinAt (P x) (-scalarCurvature (h t) x) (Set.Ici 0) t :=
    (hloc.2.2.2.2.2.2.2.2.2.2.1 x t ht).1
  have hn : HasDerivWithinAt (fun s => -P x s)
      (scalarCurvature (h t) x) (Set.Ici 0) t := by
    convert hp.neg using 1
    exact (neg_neg _).symm
  exact hn.congr_of_mem (fun s hs => (hloc.2.2.2.2.2.2.2.2.2.1 x s hs).1) ht

theorem rho_hasDerivWithinAt_Icc (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S : ℝ) (x : Pt X) (t : ℝ)
    (ht : t ∈ Set.Icc 0 S) :
    HasDerivWithinAt (ρ x) (scalarCurvature (h t) x) (Set.Icc 0 S) t :=
  (rho_hasDerivWithinAt o h U P ρ hloc x t ht.1).mono (fun _ hs => hs.1)

theorem rho_derivWithin_Icc (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S : ℝ) (hS : 0 < S)
    (x : Pt X) (t : ℝ) (ht : t ∈ Set.Icc 0 S) :
    derivWithin (ρ x) (Set.Icc 0 S) t = scalarCurvature (h t) x :=
  (rho_hasDerivWithinAt_Icc o h U P ρ hloc S x t ht).derivWithin
    (uniqueDiffOn_Icc hS t ht)

theorem density_pos (ρ : STF X) (x : Pt X) (t : ℝ) : 0 < density ρ x t :=
  Real.exp_pos _

theorem density_le_one (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    density ρ x t ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rho_nonneg o h U P ρ hloc x t ht))

theorem density_eq_det_ratio (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    density ρ x t = (gMat (h t) x).det.re / (gMat X.metric.form x).det.re := by
  have hh : 0 < (gMat (h t) x).det.re :=
    LeafProofs.L12Aux.hMat_det_re_pos (h t) x (by
      exact (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x))
  have hg : 0 < (gMat X.metric.form x).det.re :=
    LeafProofs.L12Aux.hMat_det_re_pos X.metric.form x (by
      exact (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x))
  dsimp [density]
  rw [(hloc.2.2.2.2.2.2.2.2.2.1 x t ht).1, neg_neg,
    hloc.2.2.2.2.2.2.2.2.1 x t ht, Real.exp_log (div_pos hh hg)]

theorem density_hasDerivWithinAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (density ρ x)
      (-scalarCurvature (h t) x * density ρ x t) (Set.Ici 0) t := by
  change HasDerivWithinAt (fun s => Real.exp (-ρ x s))
    (-scalarCurvature (h t) x * Real.exp (-ρ x t)) (Set.Ici 0) t
  convert (rho_hasDerivWithinAt o h U P ρ hloc x t ht).neg.exp using 1
  change -scalarCurvature (h t) x * Real.exp (-ρ x t) =
    Real.exp (-ρ x t) * -scalarCurvature (h t) x
  ring

theorem traceWith_dimension_zero (H A : Matrix (Fin 0) (Fin 0) ℂ) :
    traceWith H A = 0 := by simp [traceWith, Matrix.trace]

theorem laplacian_dimension_zero {M : ComplexManifold 0}
    (h : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) :
    laplacian h f x = 0 := traceWith_dimension_zero _ _

theorem rho_dimension_zero (X : KahlerManifold 0) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (x : Pt X) (t : ℝ) (ht : 0 ≤ t) : ρ x t = 0 := by
  have hp := hloc.2.2.2.2.2.2.2.2.1 x t ht
  have hp0 : P x t = 0 := by simpa [Matrix.det_isEmpty] using hp
  rw [(hloc.2.2.2.2.2.2.2.2.2.1 x t ht).1, hp0, neg_zero]

theorem scalarComparison_dimension_zero (X : KahlerManifold 0) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ) :
    ScalarComparison X h ρ := by
  intro T hT
  have hr := rho_dimension_zero X o h U P ρ hloc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x t ht
    rw [heatOp, rho_derivWithin_Icc o h U P ρ hloc T hT x t ht]
    simp only [scalarCurvature, laplacian, traceWith_dimension_zero, sub_zero]
  · intro ρ' _ hn _ _ x t ht
    rw [hr x t ht.1]
    exact hn x t ht
  · refine ⟨fun _ _ _ => 0, fun _ => 0, ?_, ?_⟩
    · intro j
      refine ⟨?_, ?_⟩
      · intro x
        exact contDiffOn_const
      · intro x t ht
        have hz : derivWithin (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 T) t = 0 :=
          congrFun (derivWithin_const (Set.Icc 0 T) (0 : ℝ)) t
        simp only [hr x t ht.1, sub_zero, heatOp, hz,
          laplacian_dimension_zero, le_refl, and_self]
    · intro K _ ε hε
      exact ⟨0, fun _ _ _ _ _ _ => hε.le⟩
  · intro v _ _ hv _ x t ht
    exact le_antisymm ((hv x t ⟨ht.1, ht.2.le⟩).2.trans_eq (hr x t ht.1))
      (hv x t ⟨ht.1, ht.2.le⟩).1

end Yau.F04Proof
