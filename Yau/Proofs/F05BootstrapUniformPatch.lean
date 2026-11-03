import Yau.Proofs.F05BootstrapFlatPatch
import Yau.Proofs.F05BootstrapCutoffBudget

/-! The genuine compact physical patch has a fixed eighth-power radius
budget, uniform before every artificial annulus and every candidate. -/

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_initialTimeCutoff_zero_germ {T : ℝ} (hT : 0 < T) :
    initialTimeCutoff T =ᶠ[𝓝 0] (fun _ => 0) := by
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < T/4 by positivity)] with t ht
  change t < T/4 at ht
  apply Real.smoothTransition.zero_of_nonpos
  have hRatio : (4/T)*t = (4*t)/T := by ring
  change (4/T)*t-1 ≤ 0
  rw [hRatio]
  have h : (4*t)/T ≤ 1 := (div_le_iff₀ hT).mpr (by linarith)
  linarith

theorem F05_uniform_relative_physical_patch (ν : Option (RIdx n)) {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) {K : Set (Space n)}
    (hK : IsCompact K) (hKH : K ⊆ closure (F05FlatOpen ν)) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 →
      ∀ (c : Space n) (X V : Set (Space n)) (a : Point n → Mat n)
        (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ) (F L : ℝ),
      let T := localSchauderTime δ h
      let φ : Space n → ℝ := innerPatchBump (h/8) (by positivity) c
      UniqueDiffOn ℝ X → IsOpen V → closure (F05FlatOpen ν) ∩ V ⊆ X →
      tsupport φ ⊆ V →
      HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) a M →
      (∀ j, HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) (fun z => b z j) M) →
      Elliptic (cylinder (closure (F05FlatOpen ν)) 0 T) a lam upper →
      (∀ z ∈ cylinder (closure (F05FlatOpen ν)) 0 T, z.1 ∉ K → a z = 1) →
      F05RelC2 X (Icc 0 T) u →
      (∀ j, ν = some j → ∀ x ∈ X, realCoord x j = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ X ×ˢ Icc 0 T, F05RelOp X (Icc 0 T) a b u z = f z) →
      HolderBound α ((closure (F05FlatOpen ν) ∩ V) ×ˢ Icc 0 T)
        (fun z => (u z,F05RelD X u z)) L →
      HolderBound α ((closure (F05FlatOpen ν) ∩ V) ×ˢ Icc 0 T) f F →
      F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 T)
        (fun z => initialTimeCutoff T z.2*(φ z.1*u z)) (A*(h⁻¹)^8*(F+L)) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hPatch⟩ :=
    F05_relative_flat_patch_estimate (M := M) (lam := lam) (upper := upper) ν hα hα1 hK hKH
  obtain ⟨A,hA,hBudget⟩ := F05_uniform_relative_cutoff_budget (n := n) hα hα1 hδ hδ1 hM
  refine ⟨δ,C*A,hδ,hδ1,mul_pos hC hA,?_⟩
  intro h hh hh1 c X V a b f u F L
  dsimp only
  intro hX hV hVX hSupport ha hb hEll hExterior hu hFace hEq hLow hf
  let T : ℝ := localSchauderTime δ h
  let φ : Space n → ℝ := innerPatchBump (h/8) (by positivity) c
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hTδ : T ≤ δ := by
    have hSmall : h^2/8 ≤ 1 := by nlinarith
    calc
      T = δ*(h^2/8) := by dsimp only [T,localSchauderTime]; ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hSmall hδ.le
      _ = δ := mul_one _
  obtain ⟨E,H,hφ0,hφ1,hφ2,hθ0,hθ1,hNumeric⟩ := hBudget h hh hh1 c
  have hSub : cylinder (closure (F05FlatOpen ν)) 0 T ⊆ cylinder univ 0 T :=
    fun z hz => ⟨mem_univ _,hz.2⟩
  have hResult := hPatch T a b f u X V φ (initialTimeCutoff T) F L E E E H H hT hTδ
    hX hV hVX ((innerPatchBump_contDiff (by positivity) c).of_le (by simp)) hSupport
    ((initialTimeCutoff_contDiff T).of_le (by simp)) (F05_initialTimeCutoff_zero_germ hT)
    ha hb hEll hExterior hu hFace hEq hLow hf
    (holderBound_mono hφ0 hSub) (holderBound_mono hφ1 hSub) (holderBound_mono hφ2 hSub)
    (holderBound_mono hθ0 hSub) (holderBound_mono hθ1 hSub)
  have hConst : C*(4*H*E*F+(2*H*spatialCutoffCommutatorBudget n M E E+4*H*E)*L) ≤
      (C*A)*(h⁻¹)^8*(F+L) := by
    calc
      _ ≤ C*(A*(h⁻¹)^8*(F+L)) := mul_le_mul_of_nonneg_left (hNumeric F L hf.1 hLow.1) hC.le
      _ = _ := by ring
  exact ⟨hResult.1,holderBound_mono_const hResult.2.1 hConst,
    holderBound_mono_const hResult.2.2.1 hConst,holderBound_mono_const hResult.2.2.2 hConst⟩

end Yau.Proofs.F05Aux
