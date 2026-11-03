import Yau.Proofs.F05InteriorWideGeometry
import Yau.LeafProofs.L16ExpBoundaryHolderGluing

/-! Fixed positive-time interior cylinders need only an amplitude bound and
the actual native DG oscillation estimate. No initial or artificial-rim
trace modulus enters the resulting uniform Hölder constant. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_wide_interior_oscillation_holder {B γ C F ρ s : ℝ}
    (hB : 0 ≤ B) (hγ : 0 < γ) (hγ1 : γ < 1) (hC : 0 ≤ C)
    (hF : 0 ≤ F) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8) (hs : 0 < s) :
    ∃ A : ℝ, 0 < A ∧ ∀ (T : ℝ), 0 < T → ∀ u : Point n → ℝ,
      (∀ z ∈ cylinder (region none (11/4)) 0 T, |u z| ≤ B) →
      LocalOscillationControl (F05CapOpen none (11/4)) T γ C F ρ u →
      HolderBound γ (cylinder (region none (5/2)) s T) u A := by
  let h : ℝ := min ρ (Real.sqrt s)
  have hh : 0 < h := lt_min hρ (Real.sqrt_pos.2 hs)
  let R : ℝ := h/2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRρ : R ≤ ρ := by dsimp only [R]; linarith [min_le_left ρ (Real.sqrt s)]
  have hR1 : R ≤ 1 := hRρ.trans (hρsmall.trans (by norm_num))
  let Cfar : ℝ := 2*B/(R/2)^γ
  let Cint : ℝ := C*(2 : ℝ)^γ*(2*(B/R)+F)
  let A : ℝ := 1+B+Cfar+Cint
  have hCfar : 0 ≤ Cfar := by dsimp only [Cfar]; positivity
  have hCint : 0 ≤ Cint := by dsimp only [Cint]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hBA : B ≤ A := by dsimp only [A]; linarith
  have hfarA : Cfar ≤ A := by dsimp only [A]; linarith
  have hintA : Cint ≤ A := by dsimp only [A]; linarith
  refine ⟨A,hA,?_⟩
  intro T hT u hsup hLocal
  have hWide : cylinder (region (n := n) none (5/2)) s T ⊆
      cylinder (region none (11/4)) 0 T :=
    fun _ hz => ⟨F05_region_mono (by norm_num) hz.1,hs.le.trans hz.2.1,hz.2.2⟩
  have hPair : ∀ p ∈ cylinder (region none (5/2)) s T,
      ∀ q ∈ cylinder (region none (5/2)) s T, q.2 ≤ p.2 →
        |u p-u q| ≤ A*(parabolicDistance p q)^γ := by
    intro p hp q hq ht
    let δ := parabolicDistance p q
    have hδ0 : 0 ≤ δ := parabolicDistance_nonneg p q
    by_cases hzero : δ = 0
    · have hpq : p = q := parabolicDistance_eq_zero hzero
      rw [hpq,sub_self,abs_zero]
      exact mul_nonneg hA.le (Real.rpow_nonneg (parabolicDistance_nonneg q q) _)
    have hδ : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hzero)
    by_cases hfar : R/2 ≤ δ
    · have hpair : |u p-u q| ≤ 2*B :=
        (abs_sub _ _).trans (by linarith [hsup p (hWide hp),hsup q (hWide hq)])
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ R/2) hfar hγ.le
      have hRatio : Cfar*(R/2)^γ = 2*B := by
        dsimp only [Cfar]
        field_simp
      have hstep := mul_le_mul_of_nonneg_left hpow hCfar
      rw [hRatio] at hstep
      exact hpair.trans (hstep.trans (mul_le_mul_of_nonneg_right hfarA (Real.rpow_nonneg hδ0 _)))
    have hsmall : δ < R/2 := lt_of_not_ge hfar
    have hp0 : p ∈ cylinder (region none (5/2)) 0 T :=
      ⟨hp.1,hs.le.trans hp.2.1,hp.2.2⟩
    have hbt : h ≤ Real.sqrt p.2 :=
      (min_le_right _ _).trans (Real.sqrt_le_sqrt hp.2.1)
    have hSub := F05_wide_oscCylinder_subsets hp0 hh hbt (min_le_left _ _) hρsmall
    have hRange : ∀ z ∈ dgOscCylinder p R, -B ≤ u z ∧ u z ≤ -B+2*B := by
      intro z hz
      have hzWide : z ∈ cylinder (region none (11/4)) 0 T :=
        hSub.2.1 hz
      have hb := abs_le.mp (hsup z hzWide)
      constructor <;> linarith
    have hSmall := ordered_pair_mem_oscCylinder hδ ht
    have hOsc := hLocal p R hR hRρ hSub.1 hSub.2.2 (-B) (2*B)
      (by positivity) hRange (2*δ) (by positivity) (by linarith) p hSmall.1 q hSmall.2
    have hPower := interior_amplitude_power_bound hδ0 hR hR1 hγ.le hγ1.le hC
      (by positivity : 0 ≤ B/R) hF
    have hBR : 2*(B/R)*R = 2*B := by field_simp
    rw [hBR] at hPower
    exact hOsc.trans (hPower.trans
      (mul_le_mul_of_nonneg_right hintA (Real.rpow_nonneg hδ0 _)))
  refine ⟨hA.le,?_,?_⟩
  · intro z hz
    simpa only [Real.norm_eq_abs] using (hsup z (hWide hz)).trans hBA
  · intro p hp q hq
    have hpair : |u p-u q| ≤ A*(parabolicDistance p q)^γ := by
      by_cases ht : q.2 ≤ p.2
      · exact hPair p hp q hq ht
      · calc
          _ = |u q-u p| := abs_sub_comm _ _
          _ ≤ A*(parabolicDistance q p)^γ := hPair q hq p hp (le_of_not_ge ht)
          _ = _ := by rw [parabolicDistance_symm]
    simpa only [Real.norm_eq_abs] using hpair.trans
      (mul_le_mul_of_nonneg_left (parabolicDistance_rpow_le_holderWeight hγ.le hγ1.le p q) hA.le)

end Yau.Proofs.F05Aux
