import Yau.LeafProofs.L16WordSourceDifferentiation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def wordInvariant {n : ℕ} (α T : ℝ) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ) (k : ℕ) : Prop :=
  ∀ w : List (Space n), w.length ≤ k → ∃ C : ℝ,
    SchauderBound α (cylinder Set.univ 0 T) (spatialWordDerivative w u) C ∧
    HolderBound α (cylinder Set.univ 0 T)
      (fun p => (spatialWordDerivative w u p,spatialD (spatialWordDerivative w u) p)) C ∧
    (∀ x, spatialWordDerivative w u (x,0) = 0) ∧
    ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b (spatialWordDerivative w u) p =
      wordSource a b f u w p

theorem wordInvariant_zero {n : ℕ} {α T C : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 T) u C)
    (hLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) C)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p) :
    wordInvariant α T a b f u 0 := by
  intro w hw
  cases w with
  | nil =>
    refine ⟨C,hu,hLow,hInit,?_⟩
    intro p hp
    rw [wordSource_nil]
    exact hOp p hp
  | cons e w => simp only [List.length_cons] at hw; omega

theorem wordInvariant_regularity {n : ℕ} {α T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {k : ℕ} (hI : wordInvariant α T a b f u k) (w : List (Space n)) (hw : w.length ≤ k) :
    ∃ C : ℝ, SchauderBound α (cylinder Set.univ 0 T) (spatialWordDerivative w u) C ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (spatialWordDerivative w u p,spatialD (spatialWordDerivative w u) p)) C := by
  obtain ⟨C,hC,hLow,_,_⟩ := hI w hw
  exact ⟨C,hC,hLow⟩

theorem wordInvariant_lower_slices {n : ℕ} {α T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {k : ℕ} (hI : wordInvariant α T a b f u k) (w : List (Space n)) (hw : w.length ≤ k)
    (st : List (Space n) × List (Space n)) (hst : st ∈ commutatorSplits w)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 T) :
    ContDiff ℝ 3 (fun x : Space n => spatialWordDerivative st.2 u (x,τ)) := by
  have hLength := commutatorSplits_lower_length w st hst
  apply spatialSlice_contDiff_of_c2_words 1 hτ
  intro vs hvs
  obtain ⟨C,hC,_,_,_⟩ := hI (vs++st.2) (by rw [List.length_append]; omega)
  simpa only [spatialWordDerivative_append] using hC.1

theorem wordInvariant_succ {n : ℕ} {α T M0 L lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hL : 0 ≤ L)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (ha : HolderBound α (cylinder Set.univ 0 T) a M0)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M0)
    (hLip : ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1)
    (hA : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i, ContDiffOn ℝ ∞ (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s f) (cylinder Set.univ 0 T))
    (hCoeff : ∀ s : List (Space n), ∃ M : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s a) M ∧
      ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) M)
    (hFBound : ∀ s : List (Space n), ∃ F : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s f) F)
    (k : ℕ) (hI : wordInvariant α T a b f u k) : wordInvariant α T a b f u (k+1) := by
  intro v hv
  cases v with
  | nil => exact hI [] (by simp)
  | cons e w =>
    have hw : w.length ≤ k := by simp only [List.length_cons] at hv; omega
    obtain ⟨U,hU,hULow,hUInit,hUOp⟩ := hI w hw
    have hLower (st : List (Space n) × List (Space n)) (hst : st ∈ commutatorSplits w) :
        C2 (cylinder Set.univ 0 T) (spatialWordDerivative st.2 u) := by
      have hLength := commutatorSplits_lower_length w st hst
      obtain ⟨C,hC,_,_,_⟩ := hI st.2 (by omega)
      exact hC.1
    have hCalc (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :=
      wordSource_spatial_calc hA hB hF w hLower (wordInvariant_lower_slices hI w hw) e hp
    obtain ⟨F1,hF1⟩ := wordSourceDerivative_holder hCoeff hFBound k
      (wordInvariant_regularity hI) e w hw
    have hDf : HolderBound α (cylinder Set.univ 0 T) (spatialPartial (wordSource a b f u w) e) F1 :=
      holderBound_congr_on hF1 (fun p hp => (hCalc p hp).2.symm)
    obtain ⟨M1,hDa,hDb⟩ := hCoeff [e]
    obtain ⟨D,hD,hDLow,hDInit,hDOp⟩ := spatialPartial_schauder_of_holder_derivatives
      hα hα1 hT hL hU hULow hUInit hUOp ha hb hLip hEll hK hExterior e hDa hDb hDf
      (fun p hp => (cylinder_spatialSlice_contDiff (hA []) hp.2).differentiable (by simp) p.1)
      (fun i p hp => (cylinder_spatialSlice_contDiff (hB [] i) hp.2).differentiable (by simp) p.1)
      (fun p hp => (hCalc p hp).1)
    refine ⟨D,hD,hDLow,hDInit,?_⟩
    intro p hp
    exact (hDOp p hp).trans (linearizedSpatialSource_wordSource a b f u e w p (hCalc p hp).2)

theorem wordInvariant_all {n : ℕ} {α T U M0 L lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hL : 0 ≤ L)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (huLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p)
    (ha : HolderBound α (cylinder Set.univ 0 T) a M0)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M0)
    (hLip : ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1)
    (hA : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i, ContDiffOn ℝ ∞ (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s f) (cylinder Set.univ 0 T))
    (hCoeff : ∀ s : List (Space n), ∃ M : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s a) M ∧
      ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) M)
    (hFBound : ∀ s : List (Space n), ∃ F : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s f) F) :
    ∀ k : ℕ, wordInvariant α T a b f u k := by
  intro k
  induction k with
  | zero => exact wordInvariant_zero hu huLow hInit hOp
  | succ k ih => exact wordInvariant_succ hα hα1 hT hL ha hb hLip hEll hK hExterior hA hB hF hCoeff hFBound k ih

theorem smooth_compact_coefficientWord_holder {n : ℕ} {α T : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)} (hK : IsCompact K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, a (x,t) = 1 ∧ b (x,t) = 0)
    (s : List (Space n)) : ∃ M : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s a) M ∧
      ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) M := by
  obtain ⟨CA,hCA,hA⟩ := smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK hSmooth.1
    (fun x hx t ht => (hExterior x hx t ht).1) s
  have hEach (i : Yau.RIdx n) : ∃ C : ℝ, 0 < C ∧
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative s (fun p => b p i)) C :=
    smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK (hSmooth.2 i) (c := (0 : ℝ))
      (fun x hx t ht => by rw [(hExterior x hx t ht).2]; rfl) s
  choose CB hCB hB using hEach
  let M : ℝ := 1+CA+∑ i : Yau.RIdx n, CB i
  have hSum : 0 ≤ ∑ i : Yau.RIdx n, CB i := Finset.sum_nonneg (fun i _ => (hCB i).le)
  have hCAM : CA ≤ M := by dsimp only [M]; linarith
  have hCBM (i : Yau.RIdx n) : CB i ≤ M := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := CB)
      (fun j _ => (hCB j).le) (Finset.mem_univ i)
    dsimp only [M]
    linarith
  exact ⟨M,holderBound_mono_const hA hCAM,fun i => holderBound_mono_const (hB i) (hCBM i)⟩

theorem smooth_compact_wordInvariant_all {n : ℕ} {α T U lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0)
    (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (huLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p) :
    ∀ k : ℕ, wordInvariant α T a b f u k := by
  have haExt : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, a (x,t) = 1 := fun x hx t ht => (hExterior x hx t ht).1
  have hbExt (i : Yau.RIdx n) : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, b (x,t) i = 0 :=
    fun x hx t ht => by rw [(hExterior x hx t ht).2.1]; rfl
  have hfExt : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, f (x,t) = 0 := fun x hx t ht => (hExterior x hx t ht).2.2
  have hPair : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, a (x,t) = 1 ∧ b (x,t) = 0 :=
    fun x hx t ht => ⟨(hExterior x hx t ht).1,(hExterior x hx t ht).2.1⟩
  obtain ⟨M0,L,hM0,hL,ha,hb,hLip⟩ := smooth_coefficients_common_bounds hT hα hα1 hK hSmooth hPair
  apply wordInvariant_all hα hα1 hT hL.le hu huLow hInit hOp ha hb hLip hEll hK
    (fun p hp hx => (hExterior p.1 hx p.2 hp.2).1)
    (fun s => (smooth_cylinder_spatialWordDerivative hT hK hSmooth.1 haExt s).1)
    (fun s i => (smooth_cylinder_spatialWordDerivative hT hK (hSmooth.2 i) (hbExt i) s).1)
    (fun s => (smooth_cylinder_spatialWordDerivative hT hK hfSmooth hfExt s).1)
    (smooth_compact_coefficientWord_holder hT hα hα1 hK hSmooth hPair)
  intro s
  obtain ⟨F,_,hF⟩ := smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK hfSmooth hfExt s
  exact ⟨F,hF⟩

end Yau.LeafProofs.L16Aux
