import Yau.Proofs.F05BootstrapRestrictions
import Yau.LeafProofs.L16HolderOnlyClassicalEstimate

/-! On the whole spatial space, the computed relative C2 class is the
actual native parabolic C2 class. The Hölder-only inverse gives the same
short-time estimate for every bounded zero-initial relative solution. -/

open Set
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_univ_to_native {l r : ℝ} {v : Point n → ℝ}
    (hv : F05RelC2 univ (Icc l r) v) : C2 (cylinder univ l r) v := by
  have hD (z : Point n) : F05RelD univ v z = spatialD v z := by
    simp only [F05RelD,fderivWithin_univ,spatialD]
  have hDD (z : Point n) : F05RelDD univ v z = spatialDD v z := by
    simp only [F05RelDD,F05RelD,fderivWithin_univ,spatialDD,spatialD]
  refine ⟨hv.1,hv.2.1.congr (fun z hz => (hD z).symm),
    hv.2.2.1.congr (fun z hz => (hDD z).symm),
    hv.2.2.2.1.congr (fun z hz => (F05RelT_eq_timeD v (mem_univ z.1)).symm),?_,?_⟩
  · intro z hz
    exact (hv.2.2.2.2.1 z.2 hz.2 z.1 (mem_univ _)).contDiffAt Filter.univ_mem
  · intro z hz
    have hFiber : {t | (z.1,t) ∈ cylinder univ l r} = Icc l r := by
      ext t
      simp only [cylinder,mem_prod,mem_univ,true_and,mem_ofPred_eq]
    simpa only [hFiber] using hv.2.2.2.2.2 z hz

theorem F05_relative_wholeSpace_classical_estimate {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder univ 0 T) a M →
      (∀ j, HolderBound α (cylinder univ 0 T) (fun z => b z j) M) →
      Elliptic (cylinder univ 0 T) a lam upper →
      (∀ z ∈ cylinder univ 0 T, z.1 ∉ K → a z = 1) →
      HolderBound α (cylinder univ 0 T) f F → F05RelC2 univ (Icc 0 T) u →
      (∀ z ∈ cylinder univ 0 T, |u z| ≤ B) → (∀ x, u (x,0) = 0) →
      (∀ z ∈ cylinder univ 0 T, F05RelOp univ (Icc 0 T) a b u z = f z) →
      F05RelSchauder α univ (Icc 0 T) u (C*F) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
    exists_uniform_short_classical_schauder_estimate_holder_only
      (M := M) (lam := lam) (upper := upper) hα hα1 hK
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro T a b f u F B hT hTδ ha hb hEll hExterior hf hu hBound hInit hPDE
  have hNative := F05_relative_univ_to_native hu
  obtain ⟨hSch,hLow⟩ := hEstimate T a b f u F B hT hTδ ha hb hEll hExterior hf hNative
    hBound hInit (fun z hz => by rw [← F05RelOp_eq_linearOp uniqueDiffOn_univ hNative a b hz]; exact hPDE z hz)
  have hHigh := F05_native_schauder_relative_high uniqueDiffOn_univ hSch
  refine ⟨hHigh.1,?_,hHigh.2.2.1,hHigh.2.2.2⟩
  apply holderBound_congr_on hLow
  intro z hz
  simp only [F05RelD,fderivWithin_univ,spatialD]

end Yau.Proofs.F05Aux
