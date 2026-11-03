import Yau.Proofs.F04NonlinearUniqueness

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The EXACT registered F05 output supplies its actual smooth nonlinear
 majorant. Restrict to a strictly smaller horizon before applying the
 genuine open-C1/closed-C0 nonlinear mass vanishing; no initial smoothness
 or extra majorant field is assumed. -/
theorem flow_nonlinear_comparison_from_dependencies
    (hP07 : P07) (hF03 : F03) (hG02 : G02) (hF05 : F05)
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) (v : STF X)
    (hvUSC : UpperSemicontinuousOn (fun p : Pt X × ℝ => v p.1 p.2) (univ ×ˢ Icc 0 T))
    (hvLocal : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Icc 0 T, |v x t| ≤ C)
    (hvBound : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t)
    (hvSub : NonlinearViscositySub h T v) :
    ∀ x t, t ∈ Ico 0 T → v x t = 0 := by
  obtain ⟨w,hw,hwC,hInitial,hData⟩ := hF05 n X o h U P ρ hloc T hT v hvUSC hvLocal hvBound hvSub
  intro x t ht
  let S : ℝ := (t+T)/2
  have hS : 0 < S := by dsimp only [S]; linarith [ht.1]
  have hST : S < T := by dsimp only [S]; linarith [ht.2]
  have htS : t ∈ Icc 0 S := ⟨ht.1,by dsimp only [S]; linarith [ht.2]⟩
  have hSubset : Icc (0 : ℝ) S ⊆ Ico 0 T := fun s hs => ⟨hs.1,hs.2.trans_lt hST⟩
  have hwS : SmoothSpaceTime w (Ioo 0 S) := fun c => (hw c).mono
    (Set.prod_mono (Subset.refl _) (fun s hs => ⟨hs.1,hs.2.trans hST⟩))
  have hwCS : ContinuousOn (fun p : Pt X × ℝ => w p.1 p.2) (univ ×ˢ Icc 0 S) :=
    hwC.mono (Set.prod_mono (Subset.refl _) hSubset)
  have hwBound : ∀ y s, s ∈ Icc 0 S → 0 ≤ w y s ∧ w y s ≤ ρ y s := by
    intro y s hs
    have hd := hData y s (hSubset hs)
    exact ⟨(hvBound y s ⟨hs.1,(hs.2.trans_lt hST).le⟩).1.trans hd.1,hd.2.1⟩
  have hwEq : ∀ y s, s ∈ Ioo 0 S → deriv (w y) s =
      Real.exp (-w y s)*laplacian (h s) (fun z => w z s) y+
        (1-Real.exp (-w y s))*scalarCurvature (h s) y := by
    intro y s hs
    exact (hData y s ⟨hs.1.le,hs.2.trans hST⟩).2.2 hs.1
  have hZero := smooth_nonlinear_uniqueness_from_dependencies hP07 hF03 hG02 X o h U P ρ hloc
    hS hwS hwCS hInitial hwBound hwEq
  apply le_antisymm
  · have hvw := (hData x t ht).1
    rwa [hZero x t htS] at hvw
  · exact (hvBound x t ⟨ht.1,ht.2.le⟩).1

end Yau.F04Proof
