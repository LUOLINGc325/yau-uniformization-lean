import Yau.Proofs.F05ShiftedRestart

/-! An actual solution on any late closed slab transports back through a
time translation. No regularity before the late slab is required. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_shifted_restart_pull (A : AtlasData M) (i : Fin A.count)
    (s : ℝ) (v : M.Carrier → ℝ → ℝ) :
    pull A i (F05ShiftedRestart s v) = F05TimeAffine 1 (-s) (pull A i v) := by
  funext z
  simp only [pull,F05ShiftedRestart,F05TimeAffine,F05TimeAffinePoint,one_mul,sub_eq_add_neg]

theorem F05_translated_closed_slab_schauder (A : AtlasData M) {s l r L R α C : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => t-s) (Icc l r) (Icc L R))
    (v : M.Carrier → ℝ → ℝ)
    (hv : ∀ i, SchauderBound α (cylinder (F05D A i) L R) (pull A i v) C) :
    ∀ i, SchauderBound α (cylinder (F05D A i) l r) (pull A i (F05ShiftedRestart s v)) (4*C) := by
  intro i
  have hMap1 : MapsTo (fun t : ℝ => 1*t+(-s)) (Icc l r) (Icc L R) := by
    simpa only [one_mul,sub_eq_add_neg] using hMap
  have hResult := F05_schauder_timeAffine hlr hMap1 (hv i)
  rw [F05_shifted_restart_pull]
  convert! hResult using 1
  norm_num
  ring

theorem F05_translated_closed_slab_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {s l r L R : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => t-s) (Icc l r) (Icc L R))
    (v : M.Carrier → ℝ → ℝ)
    (hv : ∀ i, C2 (cylinder (F05D A i) L R) (pull A i v))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc L R,
      derivWithin (v x) (Icc L R) t = Real.exp (-v x t)*laplacian (h (t+s)) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h (t+s)) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc l r,
      derivWithin (F05ShiftedRestart s v x) (Icc l r) t =
        Real.exp (-F05ShiftedRestart s v x t)*laplacian (h t) (fun y => F05ShiftedRestart s v y t) x+
        (1-Real.exp (-F05ShiftedRestart s v x t))*scalarCurvature (h t) x := by
  intro x hx t ht
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hFiber : {a : ℝ | (z,a) ∈ cylinder (F05D A i) L R} = Icc L R := by
    ext a
    exact and_iff_right hz
  have hDiff : DifferentiableWithinAt ℝ (v x) (Icc L R) (t-s) := by
    have hAt := (hv i).2.2.2.2.2 (z,t-s) ⟨hz,hMap ht⟩
    simpa only [hFiber,pull,hzx] using hAt
  have hChain := hDiff.hasDerivWithinAt.comp t
    (((hasDerivAt_id t).sub_const s).hasDerivWithinAt) hMap
  have hTime := hChain.derivWithin (uniqueDiffOn_Icc hlr t ht)
  have hTime' : derivWithin (F05ShiftedRestart s v x) (Icc l r) t =
      derivWithin (v x) (Icc L R) (t-s) := by
    change derivWithin (fun a => v x (a-s)) (Icc l r) t =
      derivWithin (v x) (Icc L R) (t-s)
    simpa only [Function.comp_def,id_eq,mul_one] using hTime
  have hOriginal := hEq x hx (t-s) (hMap ht)
  simp only [sub_add_cancel] at hOriginal
  exact hTime'.trans hOriginal

theorem F05_translated_closed_slab_continuous {O : Set M.Carrier} {s l r L R : ℝ}
    (hMap : MapsTo (fun t : ℝ => t-s) (Icc l r) (Icc L R))
    (v : M.Carrier → ℝ → ℝ)
    (hv : ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc L R)) :
    ContinuousOn (fun z : M.Carrier × ℝ => F05ShiftedRestart s v z.1 z.2)
      (closure O ×ˢ Icc l r) := by
  apply hv.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
  intro z hz
  change z.1 ∈ closure O ∧ z.2-s ∈ Icc L R
  exact ⟨hz.1,hMap hz.2⟩

end Yau.Proofs.F05Aux
