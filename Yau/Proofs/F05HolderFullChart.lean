import Yau.Proofs.F05HolderTransitionNeighborhood
import Yau.Proofs.F05UniformHolderGluing

/-! Value-level Hölder transport from the buffered true atlas cover to the
entire radius-two receiving charts, including their artificial rims. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_inner_holder_to_one_full_chart {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {γ : ℝ} (hγ : 0 ≤ γ) (S : ℝ) (i : Fin A.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ S →
      ∀ (q : M.Carrier → ℝ → ℝ) (P : ℝ), 0 ≤ P →
      (∀ j : Fin A.count, HolderBound γ
        (cylinder (region (A.normal j) (3/2)) 0 T) (pull A j q) P) →
      HolderBound γ (F05Q A i T) (pull A i q) (C*P) := by
  classical
  have hLocal (z : F05D A i) := F05_inner_holder_neighborhood hA i z.val z.property
  choose j r L hr hL hMap hLip using hLocal
  let G : F05D A i → ℝ := fun z => 1+(L z)^γ
  have hG (z : F05D A i) : 0 ≤ G z :=
    add_nonneg zero_le_one (Real.rpow_nonneg (hL z) γ)
  obtain ⟨C,hC,hGlue⟩ := F05_uniform_compact_holder_glue (E := ℝ)
    (F05_region_isCompact (A.normal i) 2) hγ S r G hr hG
  refine ⟨C,hC,?_⟩
  intro T hT hTS q P hP hq
  apply hGlue T hT hTS (pull A i q) P hP
  · intro p hp
    obtain ⟨j₀,hj₀⟩ := mem_iUnion.mp (hA.2.1 (F05D_lift_mem_closure hA hp.1))
    obtain ⟨w,hw,heq⟩ := hj₀
    have hSource := (hq j₀).2.1 (w,p.2)
      ⟨region_mono (A.normal j₀) (by norm_num) hw,hp.2⟩
    simpa only [pull,heq] using hSource
  · intro z
    let ψ := F05Transition A i (j z)
    have hMap' : MapsTo ψ (F05D A i ∩ Metric.closedBall z.val (r z))
        (region (A.normal (j z)) (3/2)) := fun y hy => (hMap z y hy).1
    have hLip' : ∀ x ∈ F05D A i ∩ Metric.closedBall z.val (r z),
        ∀ y ∈ F05D A i ∩ Metric.closedBall z.val (r z), ‖ψ x-ψ y‖ ≤ L z*‖x-y‖ :=
      fun x hx y hy => hLip z x hx.2 y hy.2
    have hPull := holderBound_spatial_lipschitz_pullback hγ (hL z) ψ hMap' hLip' (hq (j z))
    have hEq (p : Point n) (hp : p ∈ cylinder
        (F05D A i ∩ Metric.closedBall z.val (r z)) 0 T) :
        pull A (j z) q (ψ p.1,p.2) = pull A i q p := by
      change q (lift A (j z) (F05Transition A i (j z) p.1)) p.2 = q (lift A i p.1) p.2
      rw [(hMap z p.1 hp.1).2]
    have hActual := holderBound_congr_on hPull hEq
    simpa only [G,F05D,mul_comm] using hActual

theorem F05_inner_holder_to_full {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {γ S : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ S →
      ∀ (q : M.Carrier → ℝ → ℝ) (P : ℝ), 0 ≤ P →
      (∀ i : Fin A.count, HolderBound γ
        (cylinder (region (A.normal i) (3/2)) 0 T) (pull A i q) P) →
      ∀ i : Fin A.count, HolderBound γ (F05Q A i T) (pull A i q) (C*P) := by
  classical
  have hLocal (i : Fin A.count) := F05_inner_holder_to_one_full_chart hA hγ.le S i
  choose C hC hBudget using hLocal
  let C₀ := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀,hC₀,?_⟩
  intro T hT hTS q P hP hq i
  apply holderBound_mono_const (hBudget i T hT hTS q P hP hq)
  apply mul_le_mul_of_nonneg_right _ hP
  have hCi := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin A.count))) => (hC k).le) (Finset.mem_univ i)
  dsimp only [C₀]
  linarith

end Yau.Proofs.F05Aux
