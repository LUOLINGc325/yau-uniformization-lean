import Yau.Proofs.F05BootstrapNative
import Yau.LeafProofs.L16BoundaryTimeContinuation

/-! Actual restrictions to positive-time closed physical cylinders retain
their one-sided derivative at both endpoints. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_timeD_restrict_interval {X : Set (Space n)} {l r L R : ℝ}
    (hlr : l < r) (hLl : L ≤ l) (hrR : r ≤ R) {v : Point n → ℝ}
    (hv : C2 (cylinder X L R) v) {z : Point n} (hz : z ∈ cylinder X l r) :
    timeD (cylinder X l r) v z = timeD (cylinder X L R) v z := by
  have hzBig : z ∈ cylinder X L R := ⟨hz.1,hLl.trans hz.2.1,hz.2.2.trans hrR⟩
  have hSmall : {t | (z.1,t) ∈ cylinder X l r} = Icc l r := by
    ext t
    simp only [cylinder,mem_prod,hz.1,true_and,mem_ofPred_eq]
  have hBig : {t | (z.1,t) ∈ cylinder X L R} = Icc L R := by
    ext t
    simp only [cylinder,mem_prod,hz.1,true_and,mem_ofPred_eq]
  have hDiff : DifferentiableWithinAt ℝ (fun t => v (z.1,t)) (Icc L R) z.2 := by
    simpa only [hBig] using hv.2.2.2.2.2 z hzBig
  have hEq := (hDiff.hasDerivWithinAt.mono (Icc_subset_Icc hLl hrR)).derivWithin
    (uniqueDiffOn_Icc hlr z.2 hz.2)
  simpa only [timeD,hSmall,hBig] using hEq

theorem F05_c2_restrict_interval {X : Set (Space n)} {l r L R : ℝ}
    (hlr : l < r) (hLl : L ≤ l) (hrR : r ≤ R) {v : Point n → ℝ}
    (hv : C2 (cylinder X L R) v) : C2 (cylinder X l r) v := by
  have hSub : cylinder X l r ⊆ cylinder X L R :=
    fun _ hz => ⟨hz.1,hLl.trans hz.2.1,hz.2.2.trans hrR⟩
  refine ⟨hv.1.mono hSub,hv.2.1.mono hSub,hv.2.2.1.mono hSub,?_,
    fun z hz => hv.2.2.2.2.1 z (hSub hz),?_⟩
  · exact (hv.2.2.2.1.mono hSub).congr
      (fun z hz => F05_timeD_restrict_interval hlr hLl hrR hv hz)
  · intro z hz
    exact (hv.2.2.2.2.2 z (hSub hz)).mono (fun t ht => hSub ht)

theorem F05_schauder_restrict_interval {X : Set (Space n)} {α C l r L R : ℝ}
    (hlr : l < r) (hLl : L ≤ l) (hrR : r ≤ R) {v : Point n → ℝ}
    (hv : SchauderBound α (cylinder X L R) v C) : SchauderBound α (cylinder X l r) v C := by
  have hSub : cylinder X l r ⊆ cylinder X L R :=
    fun _ hz => ⟨hz.1,hLl.trans hz.2.1,hz.2.2.trans hrR⟩
  refine ⟨F05_c2_restrict_interval hlr hLl hrR hv.1,hv.2.1,
    fun z hz => hv.2.2.1 z (hSub hz),holderBound_mono hv.2.2.2.1 hSub,?_⟩
  exact holderBound_congr_on (holderBound_mono hv.2.2.2.2 hSub)
    (fun z hz => (F05_timeD_restrict_interval hlr hLl hrR hv.1 hz).symm)

theorem F05_native_schauder_relative_high {X : Set (Space n)} {α C l r : ℝ}
    (hX : UniqueDiffOn ℝ X) {v : Point n → ℝ} (hv : SchauderBound α (cylinder X l r) v C) :
    F05RelC2 X (Icc l r) v ∧
      (∀ z ∈ X ×ˢ Icc l r, |v z| ≤ C ∧ ‖F05RelD X v z‖ ≤ C) ∧
      HolderBound α (X ×ˢ Icc l r) (F05RelDD X v) C ∧
      HolderBound α (X ×ˢ Icc l r) (F05RelT (Icc l r) v) C := by
  refine ⟨F05_native_c2_to_relative hX hv.1,?_,?_,?_⟩
  · intro z hz
    rw [F05RelD_eq_spatialD (hX z.1 hz.1) ((hv.1.2.2.2.2.1 z hz).differentiableAt (by norm_num))]
    exact hv.2.2.1 z hz
  · exact holderBound_congr_on hv.2.2.2.1 (fun z hz =>
      (F05RelDD_eq_spatialDD hX hz.1 (fun x hx => hv.1.2.2.2.2.1 (x,z.2) ⟨hx,hz.2⟩)).symm)
  · exact holderBound_congr_on hv.2.2.2.2 (fun z hz => (F05RelT_eq_timeD v hz.1).symm)

theorem F05_native_local_relative_high (ν : Option (RIdx n)) {T α K : ℝ}
    {v : Point n → ℝ} (hv : SchauderBound α (cylinder (region ν 2) 0 T) v K)
    {r s : ℝ} (hr : 0 < r) (hr2 : r < 2) (hs : 0 ≤ s) (hsT : s < T) :
    F05RelC2 (region ν r) (Icc s T) v ∧
      (∀ z ∈ region ν r ×ˢ Icc s T, |v z| ≤ K ∧ ‖F05RelD (region ν r) v z‖ ≤ K) ∧
      HolderBound α (region ν r ×ˢ Icc s T) (F05RelDD (region ν r) v) K ∧
      HolderBound α (region ν r ×ˢ Icc s T) (F05RelT (Icc s T) v) K :=
  F05_native_schauder_relative_high (F05_region_uniqueDiffOn ν hr)
    (F05_schauder_restrict_interval hsT hs le_rfl
      (Yau.LeafProofs.L16BoundaryTimeAux.schauderBound_mono_space
        (F05_region_mono hr2.le) hv))

end Yau.Proofs.F05Aux
