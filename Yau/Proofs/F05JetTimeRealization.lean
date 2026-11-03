import Yau.Proofs.F05JetFTC
import Yau.Proofs.F05BCFExtension

/-! The temporal FTC equation gives the actual one-sided derivative, including
both closed-time endpoints. No derivative realization is assumed. -/

open Set MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05LocalFTCGraph_hasDerivWithinAt_time (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (z : F05D A i) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => u.val.1 (F05TimePath A i hT z.property r))
      (u.val.2.2.2.val.1 (F05TimePath A i hT z.property t)) (Icc 0 T) t := by
  let k : ℝ → ℝ := fun r => u.val.2.2.2.val.1 (F05TimePath A i hT z.property r)
  let v₀ := u.val.1 ⟨(z.val,0),z.property,le_rfl,hT⟩
  have hk : Continuous k := u.val.2.2.2.val.1.continuous.comp
    (F05TimePath_continuous A i hT z.property)
  have hI : HasDerivAt (fun r => ∫ s in (0 : ℝ)..r, k s) (k t) t :=
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hS : HasDerivAt (fun r => v₀ + ∫ s in (0 : ℝ)..r, k s) (k t) t := by
    exact hI.const_add v₀
  apply hS.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  have hPath : F05TimePath A i hT z.property r = ⟨(z.val,r),z.property,hr⟩ :=
    Subtype.ext (F05TimePath_eq A i hT z.property hr)
  rw [hPath]
  have hFTC := F05LocalFTCGraph_time A i α hT u z ⟨0,le_rfl,hT⟩ ⟨r,hr⟩
  change u.val.1 ⟨(z.val,r),z.property,hr⟩ - v₀ = ∫ s in (0 : ℝ)..r, k s at hFTC
  linarith

theorem F05LocalFTCGraph_derivWithin_time (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05LocalFTCGraph A i α hT.le)
    (z : F05D A i) (t : ℝ) (ht : t ∈ Icc 0 T) :
    derivWithin (fun r => u.val.1 (F05TimePath A i hT.le z.property r)) (Icc 0 T) t =
      u.val.2.2.2.val.1 (F05TimePath A i hT.le z.property t) :=
  (F05LocalFTCGraph_hasDerivWithinAt_time A i α hT.le u z t ht).derivWithin
    (uniqueDiffOn_Icc hT t ht)

theorem F05LocalFTCGraph_hasDerivWithinAt_raw_time (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    {z : Space n} (hz : z ∈ F05D A i) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => F05BCFFun u.val.1 (z,r))
      (F05BCFFun u.val.2.2.2.val.1 (z,t)) (Icc 0 T) t := by
  have hh := F05LocalFTCGraph_hasDerivWithinAt_time A i α hT u ⟨z,hz⟩ t ht
  have hK : u.val.2.2.2.val.1 (F05TimePath A i hT hz t) =
      F05BCFFun u.val.2.2.2.val.1 (z,t) := by
    rw [← F05TimePath_eq A i hT hz ht,F05BCFFun_apply]
  rw [hK] at hh
  apply hh.congr_of_mem _ ht
  intro r hr
  rw [← F05TimePath_eq A i hT hz hr,F05BCFFun_apply]

theorem F05LocalFTCGraph_timeD_raw (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05LocalFTCGraph A i α hT.le)
    {z : Space n} (hz : z ∈ F05D A i) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeD (F05Q A i T) (F05BCFFun u.val.1) (z,t) = F05BCFFun u.val.2.2.2.val.1 (z,t) := by
  have hFiber : {r : ℝ | (z,r) ∈ F05Q A i T} = Icc 0 T := by
    ext r
    change (z ∈ F05D A i ∧ r ∈ Icc 0 T) ↔ r ∈ Icc 0 T
    exact and_iff_right hz
  unfold timeD
  rw [hFiber]
  exact (F05LocalFTCGraph_hasDerivWithinAt_raw_time A i α hT.le u hz ht).derivWithin
    (uniqueDiffOn_Icc hT t ht)

end Yau.Proofs.F05Aux
