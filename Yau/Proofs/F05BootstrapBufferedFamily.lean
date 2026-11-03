import Yau.Proofs.F05BootstrapBufferedRaw

/-! A uniform genuine patch family around every point of an arbitrary
compact receiving cap and positive-time slab. Constants precede every
coefficient, candidate and terminal time. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_physical_schauder_family (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase)
    {α M lam upper r s0 s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hr : 0 < r) (hrχ : r < χ.rIn) (hs : s0 < s) :
    ∃ (d : ℝ) (hd : 0 < d) (sL δ C : ℝ), d ≤ 1 ∧ r+d < χ.rIn ∧ s0 < sL ∧ sL < s ∧
      0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ localSchauderTime δ d ≤ s-sL ∧
      ∀ (T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ), s < T0 →
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, |u z| ≤ B) →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      HolderBound α (region ν (r+3*d/4) ×ˢ Icc sL T0)
        (fun z => (u z,F05RelD (region ν Rbase) u z)) (C*(B+F)) ∧
      (∀ z ∈ region ν (r+d) ×ˢ Icc sL T0, F05RelHigh (region ν Rbase) (Icc s0 T0) u z ≤ C*(B+F)) ∧
      ∀ (τ : ℝ) (c : Space n), τ ∈ Icc s T0 → ‖c‖ ≤ r →
        F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 (localSchauderTime δ d))
          (classicalInteriorPatch δ d (τ-localSchauderTime δ d) hd c u) (C*(B+F)) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  let d := min (1/2) (min ((χ.rIn-r)/2) (Real.sqrt (s-s0)/2))
  let R := r+d
  let dPatch := R-r
  let S := r+3*d/4
  let sL := (s0+s)/2
  let ρ := d/8
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hdHalf : d ≤ 1/2 := min_le_left _ _
  have hd1 : d ≤ 1 := by linarith
  have hdRadius : d ≤ (χ.rIn-r)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdTime : d ≤ Real.sqrt (s-s0)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hRχ : R < χ.rIn := by dsimp only [R]; linarith
  have hdPatchEq : dPatch = d := by dsimp only [dPatch,R]; ring
  have hdPatch : 0 < dPatch := by rwa [hdPatchEq]
  have hR0 : 0 < R := by dsimp only [R]; positivity
  have hs0L : s0 < sL := by dsimp only [sL]; linarith
  have hsLs : sL < s := by dsimp only [sL]; linarith
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp only [ρ]; linarith
  obtain ⟨CK,hCK,hHigh⟩ := F05_buffered_high_on_receiving_slab (M := M) (lam := lam) (upper := upper)
    ν χ hχ hα hα1 hM hR0 hRχ hs0L
  obtain ⟨δ,A,hδ,hδ1,hA,hPatches⟩ := F05_uniform_buffered_original_physical_patches
    (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM
  let L0 := 8*(ρ^(1-α)*CK+ρ^(-1-α))
  let W := A*(dPatch⁻¹)^8*(1+L0)
  let C := 1+L0+CK+W
  have hL0 : 0 ≤ L0 := by dsimp only [L0]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hL0C : L0 ≤ C := by dsimp only [C]; linarith
  have hCKC : CK ≤ C := by dsimp only [C]; linarith
  have hWC : W ≤ C := by dsimp only [C]; linarith
  have hGapTime : localSchauderTime δ d ≤ s-sL := by
    have hSq := pow_le_pow_left₀ hd.le hdTime 2
    have hId := Real.sq_sqrt (sub_nonneg.mpr hs.le)
    have hdSq : d^2/8 ≤ s-sL := by dsimp only [sL]; nlinarith
    exact (div_le_div_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 (sq_nonneg d)) (by norm_num)).trans hdSq
  refine ⟨dPatch,hdPatch,sL,δ,C,by rwa [hdPatchEq],by simpa only [hdPatchEq] using hRχ,
    hs0L,hsLs,hδ,hδ1,hC,by simpa only [hdPatchEq] using hGapTime,?_⟩
  intro T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  let D := B+F
  have hB0 : 0 ≤ B := by
    have hZero : ((0,sL) : Point n) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
      refine ⟨?_,hs0L.le,hsLs.le.trans hsT.le⟩
      cases ν <;> simpa [region,realCoord] using hRbase.le
    exact (abs_nonneg _).trans (hB (0,sL) hZero)
  have hD : 0 ≤ D := add_nonneg hB0 hf.1
  have hBLe : B ≤ D := le_add_of_nonneg_right hf.1
  have hFLe : F ≤ D := le_add_of_nonneg_left hB0
  have hRaw := hHigh T0 a b f u F B hEll ha hb hf hu hB hFace hEq
  have hX := F05_region_uniqueDiffOn ν hRbase
  have hY := F05_region_uniqueDiffOn ν hR0
  have hTime := uniqueDiffOn_Icc (hsLs.trans hsT)
  have hSpace : region ν R ⊆ region ν Rbase := F05_region_mono (hRχ.le.trans (χ.rIn_lt_rOut.le.trans hχ))
  have hI : Icc sL T0 ⊆ Icc s0 T0 := fun t ht => ⟨hs0L.le.trans ht.1,ht.2⟩
  have hSub := prod_mono hSpace hI
  have huClosed := F05_relative_c2_restrict hX hY hTime hSpace hI hu
  have hJets (z : Point n) (hz : z ∈ region ν R ×ˢ Icc sL T0) :=
    F05_relative_restriction_jets hX hY hTime hSpace hI hu hz
  have hK : ∀ z ∈ region ν R ×ˢ Icc sL T0,
      ‖F05RelDD (region ν R) u z‖ ≤ CK*D ∧ |F05RelT (Icc sL T0) u z| ≤ CK*D := by
    intro z hz
    rw [(hJets z hz).2.1,(hJets z hz).2.2]
    exact ⟨(le_max_left _ _).trans (hRaw z hz),(le_max_right _ _).trans (hRaw z hz)⟩
  have hLowRaw := F05_relative_cap_low_interpolation ν hα hα1 hR0 hρ hρ1
    (show S+ρ ≤ R by dsimp only [S,ρ,R]; linarith) hB0 (mul_nonneg hCK.le hD) huClosed
    (fun z hz => hB z (hSub hz)) hK
  have hLow : HolderBound α (region ν S ×ˢ Icc sL T0)
      (fun z => (u z,F05RelD (region ν Rbase) u z)) (L0*D) := by
    apply holderBound_mono_const (holderBound_congr_on hLowRaw ?_)
    · have hScale := mul_le_mul_of_nonneg_left hBLe (Real.rpow_nonneg hρ.le (-1-α))
      dsimp only [L0]
      nlinarith
    · intro z hz
      change (u z,F05RelD (region ν R) u z) = (u z,F05RelD (region ν Rbase) u z)
      rw [(hJets z ⟨F05_region_mono (by dsimp only [S,R]; linarith) hz.1,hz.2⟩).1]
  refine ⟨by simpa only [hdPatchEq] using holderBound_mono_const hLow (mul_le_mul_of_nonneg_right hL0C hD),?_,?_⟩
  · intro z hz
    have hzR : z ∈ region ν R ×ˢ Icc sL T0 := by simpa only [hdPatchEq] using hz
    exact (hRaw z hzR).trans (mul_le_mul_of_nonneg_right hCKC hD)
  · intro τ c hτ hc
    have hRG : R-r = d := by dsimp only [R]; ring
    have hPatch := hPatches s0 T0 a b f u F hEll ha hb hf hu hFace hEq
      r R sL τ c (L0*D) hr.le (by dsimp only [R]; linarith) hRχ.le (by rwa [hRG]) hs0L.le
      ⟨by rw [hRG]; linarith [hτ.1],hτ.2⟩ hc (by simpa only [hRG] using hLow)
    have hPatch' : F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 (localSchauderTime δ dPatch))
        (classicalInteriorPatch δ dPatch (τ-localSchauderTime δ dPatch) hdPatch c u)
        (A*(dPatch⁻¹)^8*(F+L0*D)) := hPatch
    have hConst : A*(dPatch⁻¹)^8*(F+L0*D) ≤ C*D := by
      have hSource : F+L0*D ≤ (1+L0)*D := by nlinarith
      calc
        _ ≤ A*(dPatch⁻¹)^8*((1+L0)*D) := mul_le_mul_of_nonneg_left hSource (by positivity)
        _ = W*D := by dsimp only [W]; ring
        _ ≤ C*D := mul_le_mul_of_nonneg_right hWC hD
    exact ⟨hPatch'.1,holderBound_mono_const hPatch'.2.1 hConst,
      holderBound_mono_const hPatch'.2.2.1 hConst,holderBound_mono_const hPatch'.2.2.2 hConst⟩

end Yau.Proofs.F05Aux
