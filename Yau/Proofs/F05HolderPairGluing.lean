import Yau.Proofs.F05HolderPairBounds
import Yau.Proofs.F05HolderOscillationGeometry
import Yau.LeafProofs.L16ExpBoundaryHolderGluing

/-! The native pair argument localized between genuine spatial buffers.
The artificial radius-two rim carries no boundary modulus. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_ordered_buffered_pair (k : Option (RIdx n)) {B K L γ C F ρ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : ℝ), 0 < T → ∀ (u G : Point n → ℝ),
      (∀ z ∈ cylinder (region k 2) 0 T, |u z| ≤ B) →
      (∀ z ∈ cylinder (region k (7/4)) 0 T, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1)) →
      (∀ p ∈ cylinder (region k (7/4)) 0 T, ∀ q ∈ cylinder (region k (7/4)) 0 T,
        |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|)) →
      LocalOscillationControl (F05CapOpen k 2) T γ C F ρ u →
      ∀ p ∈ cylinder (region k (3/2)) 0 T, ∀ q ∈ cylinder (region k (3/2)) 0 T, q.2 ≤ p.2 →
        |u p-u q| ≤ A*(parabolicDistance p q)^γ := by
  let H := outerAmplitude B K L ρ
  have hH : 0 < H := outerAmplitude_pos hB hK hL hρ
  let Cfar : ℝ := 2*B/(ρ/16)^γ
  let Cnear : ℝ := 512*K+2*L
  let Cint : ℝ := C*(2 : ℝ)^γ*(2*H+F)
  have hCfar : 0 ≤ Cfar := by dsimp [Cfar]; positivity
  have hCnear : 0 ≤ Cnear := by dsimp [Cnear]; positivity
  have hCint : 0 ≤ Cint := by dsimp [Cint]; positivity
  let A : ℝ := 1+Cfar+Cnear+Cint
  have hA : 0 < A := by dsimp [A]; positivity
  have hfarA : Cfar ≤ A := by dsimp [A]; linarith
  have hnearA : Cnear ≤ A := by dsimp [A]; linarith
  have hintA : Cint ≤ A := by dsimp [A]; linarith
  refine ⟨A,hA,?_⟩
  intro T hT u G hsup he hLip hLocal p hp q hq ht
  have hρ1 : ρ ≤ 1 := hρsmall.trans (by norm_num)
  have hMid : cylinder (region k (3/2)) 0 T ⊆ cylinder (region k (7/4)) 0 T :=
    fun _ hz => ⟨F05_region_mono (by norm_num) hz.1,hz.2⟩
  have hWide : cylinder (region k (7/4)) 0 T ⊆ cylinder (region k 2) 0 T :=
    fun _ hz => ⟨F05_region_mono (by norm_num) hz.1,hz.2⟩
  have hsupMid : ∀ z ∈ cylinder (region k (7/4)) 0 T, |u z| ≤ B :=
    fun z hz => hsup z (hWide hz)
  let δ := parabolicDistance p q
  have hδ0 : 0 ≤ δ := parabolicDistance_nonneg p q
  by_cases hzero : δ = 0
  · have hpq : p = q := parabolicDistance_eq_zero hzero
    have hleft : |u p-u q| = 0 := by rw [hpq,sub_self,abs_zero]
    rw [hleft]
    exact mul_nonneg hA.le (Real.rpow_nonneg hδ0 _)
  have hδ : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hzero)
  by_cases hfar : ρ/16 ≤ δ
  · have hpair : |u p-u q| ≤ 2*B := (abs_sub _ _).trans (by linarith [hsupMid p (hMid hp),hsupMid q (hMid hq)])
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ρ/16) hfar hγ.le
    have hRatio : Cfar*(ρ/16)^γ = 2*B := by
      dsimp [Cfar]
      field_simp
    have hstep := mul_le_mul_of_nonneg_left hpow hCfar
    rw [hRatio] at hstep
    exact hpair.trans (hstep.trans (mul_le_mul_of_nonneg_right hfarA (Real.rpow_nonneg hδ0 _)))
  have hsmall : δ < ρ/16 := lt_of_not_ge hfar
  have hδ1 : δ ≤ 1 := by linarith
  have hCap : 16*δ < ρ := by linarith
  let h : ℝ := min (F05FaceGauge k p.1) (min (Real.sqrt p.2) ρ)
  have hbd : h ≤ F05FaceGauge k p.1 := min_le_left _ _
  have hbt : h ≤ Real.sqrt p.2 := (min_le_right _ _).trans (min_le_left _ _)
  have hbρ : h ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hnear : h ≤ 16*δ
  · have hNearCase : F05FaceGauge k p.1 ≤ 16*δ ∨ p.2 ≤ 256*δ^2 := by
      by_cases hbdNear : F05FaceGauge k p.1 ≤ 16*δ
      · exact Or.inl hbdNear
      · right
        have hroot : Real.sqrt p.2 ≤ 16*δ := by
          by_contra hn
          have hh : 16*δ < h := lt_min (lt_of_not_ge hbdNear) (lt_min (lt_of_not_ge hn) hCap)
          exact not_lt_of_ge hnear hh
        nlinarith [Real.sq_sqrt hp.2.1,Real.sqrt_nonneg p.2]
    have hpair := F05_near_pair_linear_bound hK hL he hLip (hMid hp) (hMid hq) ht hδ1 hNearCase
    have hpow := small_linear_le_rpow hδ0 hδ1 hγ.le hγ1.le
    exact hpair.trans ((mul_le_mul_of_nonneg_left hpow hCnear).trans
      (mul_le_mul_of_nonneg_right hnearA (Real.rpow_nonneg hδ0 _)))
  · have hfarBuffer : 16*δ < h := lt_of_not_ge hnear
    have hh : 0 < h := by linarith
    let R : ℝ := h/2
    have hR : 0 < R := by dsimp [R]; positivity
    have hRρ : R ≤ ρ := by dsimp [R]; linarith
    have hR1 : R ≤ 1 := hRρ.trans hρ1
    have hSub := F05_buffered_oscCylinder_subsets hp hh hbd hbt hbρ hρsmall
    have hCases : h = F05FaceGauge k p.1 ∨ h = Real.sqrt p.2 ∨ h = ρ := by
      dsimp only [h]
      by_cases hd : F05FaceGauge k p.1 ≤ min (Real.sqrt p.2) ρ
      · exact Or.inl (min_eq_left hd)
      · right
        rw [min_eq_right (le_of_not_ge hd)]
        by_cases hs : Real.sqrt p.2 ≤ ρ
        · exact Or.inl (min_eq_left hs)
        · exact Or.inr (min_eq_right (le_of_not_ge hs))
    have hAmpCase : F05FaceGauge k p.1 ≤ 2*R ∨ p.2 ≤ 4*R^2 ∨ ρ ≤ 2*R := by
      rcases hCases with hd | hs | hcap
      · left
        dsimp [R]
        linarith
      · right; left
        have hsq := Real.sq_sqrt hp.2.1
        dsimp [R]
        nlinarith
      · right; right
        dsimp [R]
        linarith
    have hAmp : ∀ z ∈ dgOscCylinder p R, |u z-u p| ≤ H*R :=
      F05_outer_center_amplitude hB hK hL hρ hsupMid he hLip (hMid hp) hR hR1 hSub.2.1 hAmpCase
    have hRange : ∀ z ∈ dgOscCylinder p R,
        u p-H*R ≤ u z ∧ u z ≤ (u p-H*R)+2*H*R := by
      intro z hz
      have hb := abs_le.mp (hAmp z hz)
      constructor <;> linarith
    have hSmallR : 2*δ ≤ R := by dsimp [R]; linarith
    have hSmall := ordered_pair_mem_oscCylinder hδ ht
    have hOsc := hLocal p R hR hRρ hSub.1 hSub.2.2 (u p-H*R) (2*H*R)
      (by positivity) hRange (2*δ) (by positivity) hSmallR p hSmall.1 q hSmall.2
    have hPower := interior_amplitude_power_bound hδ0 hR hR1 hγ.le hγ1.le hC hH.le hF
    exact hOsc.trans (hPower.trans (mul_le_mul_of_nonneg_right hintA (Real.rpow_nonneg hδ0 _)))


theorem F05_buffered_holder_from_error_and_interior (k : Option (RIdx n)) {B K L γ C F ρ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (T : ℝ), 0 < T → ∀ (u G : Point n → ℝ),
      (∀ z ∈ cylinder (region k 2) 0 T, |u z| ≤ B) →
      (∀ z ∈ cylinder (region k (7/4)) 0 T, |u z-G z| ≤ K*min z.2 (F05FaceGauge k z.1)) →
      (∀ p ∈ cylinder (region k (7/4)) 0 T, ∀ q ∈ cylinder (region k (7/4)) 0 T,
        |G p-G q| ≤ L*(‖p.1-q.1‖+|p.2-q.2|)) →
      LocalOscillationControl (F05CapOpen k 2) T γ C F ρ u → HolderBound γ (cylinder (region k (3/2)) 0 T) u C₀ := by
  obtain ⟨A,hA,hPair⟩ := F05_ordered_buffered_pair k hB hK hL hγ hγ1 hC hF hρ hρsmall
  let C₀ : ℝ := 1+B+A
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hBC : B ≤ C₀ := by dsimp [C₀]; linarith
  have hAC : A ≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨C₀,hC₀,?_⟩
  intro T hT u G hsup he hLip hLocal
  have hSupSmall : ∀ z ∈ cylinder (region k (3/2)) 0 T, |u z| ≤ B :=
    fun z hz => hsup z ⟨F05_region_mono (by norm_num) hz.1,hz.2⟩
  refine ⟨hC₀.le,?_,?_⟩
  · intro z hz
    simpa only [Real.norm_eq_abs] using (hSupSmall z hz).trans hBC
  · intro p hp q hq
    have hpair : |u p-u q| ≤ A*(parabolicDistance p q)^γ := by
      by_cases ht : q.2 ≤ p.2
      · exact hPair T hT u G hsup he hLip hLocal p hp q hq ht
      · calc
          _ = |u q-u p| := abs_sub_comm _ _
          _ ≤ A*(parabolicDistance q p)^γ := hPair T hT u G hsup he hLip hLocal q hq p hp (le_of_not_ge ht)
          _ = _ := by rw [parabolicDistance_symm]
    have hweight : 0 ≤ holderWeight γ p q := by dsimp [holderWeight]; positivity
    simpa only [Real.norm_eq_abs] using hpair.trans
      ((mul_le_mul_of_nonneg_left (parabolicDistance_rpow_le_holderWeight hγ.le hγ1.le p q) hA.le).trans
        (mul_le_mul_of_nonneg_right hAC hweight))


end Yau.Proofs.F05Aux
