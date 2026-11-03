import Yau.Proofs.F05JetCompatibility
import Yau.Proofs.F05JetExtensionInitial
import Yau.Proofs.F05PartitionModel

/-! A literal finite sum of inner plateau extensions realizes the compatible
physical values on the manifold. Nothing outside the physical set is quotiented. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05InnerPlateau (n : ℕ) : Space n → ℝ := innerPatchBump (1/2) (by norm_num) 0

theorem F05InnerPlateau_contDiff : ContDiff ℝ ∞ (F05InnerPlateau n) :=
  innerPatchBump_contDiff (by norm_num) 0

theorem F05InnerPlateau_tsupport : tsupport (F05InnerPlateau n) ⊆ Metric.closedBall 0 1 := by
  unfold F05InnerPlateau
  rw [(innerPatchBump (1/2) (by norm_num) (0 : Space n)).tsupport_eq]
  change Metric.closedBall 0 (3*(1/2 : ℝ)/2) ⊆ Metric.closedBall 0 1
  exact Metric.closedBall_subset_closedBall (by norm_num)

theorem F05LocalJetExtension_value_on_model (A : AtlasData M) (i : Fin A.count)
    {α T : ℝ} (φ : Space n → ℝ) (u : F05JetComponent α (F05Q A i T))
    {p : Point n} (hp : p.1 ∈ closure (F05ModelOpen A i)) :
    F05LocalJetExtension A i φ u p = F05CutoffJetValue φ u p := by
  cases hν : A.normal i with
  | none => simp only [F05LocalJetExtension,hν]
  | some j =>
    rw [F05ModelClosed_some A i hν] at hp
    have hn : 0 ≤ inner ℝ (-realVec j) p.1 := hp
    simp only [F05LocalJetExtension,hν,halfSpaceSecondOrderExtension,ite_eq_left hn]

theorem F05InnerExtension_value (A : AtlasData M) (i : Fin A.count) (α T : ℝ)
    (u : F05JetComponent α (F05Q A i T)) (w : Space n) (hw : w ∈ F05D A i)
    (hn : ‖w‖ ≤ 1/4) (t : ℝ) :
    F05LocalJetExtension A i (F05InnerPlateau n) u (w,t) = F05BCFFun u.1 (w,t) := by
  have hPlateau : F05InnerPlateau n w = 1 := by
    apply innerPatchBump_eq_one (by norm_num)
    rw [sub_zero]
    exact hn.trans (by norm_num)
  have hExt := @F05LocalJetExtension_value_on_model n M A i α T (F05InnerPlateau n) u
    (w,t) (F05D_subset_model_closure A i hw)
  rw [hExt]
  unfold F05CutoffJetValue
  rw [hPlateau,one_mul]

def F05CanonicalJetFunction (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT) : M.Carrier → ℝ → ℝ :=
  fun x t => ∑ i, χ i x * F05LocalJetExtension A i (F05InnerPlateau n)
    (u.val i).val (F05Coord A i x,t)

theorem F05CanonicalJetFunction_initial (A : AtlasData M)
    (χ : Fin A.count → M.Carrier → ℝ) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (u : F05CompatibleJetGraph A α hT) (x : M.Carrier) :
    F05CanonicalJetFunction A χ α hT u x 0 = 0 := by
  simp only [F05CanonicalJetFunction,F05_local_extension_initial_value,mul_zero,Finset.sum_const_zero]

theorem F05CanonicalJetFunction_value {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    (j : Fin A.count) {z : Space n} (hz : z ∈ F05D A j) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05CanonicalJetFunction A χ α hT u (lift A j z) t =
      F05BCFFun (u.val j).val.1 (z,t) := by
  let x := lift A j z
  have hx : x ∈ closure O := F05D_lift_mem_closure hA hz
  have hTerm (i : Fin A.count) : χ i x * F05LocalJetExtension A i (F05InnerPlateau n)
      (u.val i).val (F05Coord A i x,t) = χ i x * F05BCFFun (u.val j).val.1 (z,t) := by
    by_cases hχx : χ i x = 0
    · simp only [hχx,zero_mul]
    · have hxS : x ∈ tsupport (χ i) := subset_tsupport (χ i) hχx
      obtain ⟨w,hw,hwx⟩ := hχ.2.2.1 i hxS
      have hn : ‖w‖ ≤ 1/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      have hw3 : w ∈ Metric.ball (0 : Space n) 3 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hn.trans_lt (by norm_num : (1/4 : ℝ) < 3)
      obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 i
      have hFace := (hPhysical w hw3).2.1
      rw [hwx] at hFace
      have hwD : w ∈ F05D A i := ⟨hn.trans (by norm_num),hFace.mp hx⟩
      have hCoord : F05Coord A i x = w := by
        rw [← hwx]
        exact F05Coord_lift hA hwD
      let p : F05OverlapPoint A T :=
        ⟨i,j,⟨w,hwD⟩,⟨z,hz⟩,⟨t,ht⟩,hwx⟩
      have hEqualRaw : F05BCFFun (u.val i).val.1 (w,t) = F05BCFFun (u.val j).val.1 (z,t) := by
        rw [F05BCFFun_apply (u.val i).val.1 ⟨(w,t),hwD,ht⟩,
          F05BCFFun_apply (u.val j).val.1 ⟨(z,t),hz,ht⟩]
        exact F05CompatibleJetGraph_value A α hT u p
      have hValue : F05LocalJetExtension A i (F05InnerPlateau n) (u.val i).val
          (F05Coord A i x,t) = F05BCFFun (u.val j).val.1 (z,t) := by
        rw [hCoord]
        exact (F05InnerExtension_value A i α T (u.val i).val w hwD hn t).trans hEqualRaw
      rw [hValue]
  obtain ⟨V,_,hKV,hSum⟩ := hχ.2.2.2
  change (∑ i, χ i x * F05LocalJetExtension A i (F05InnerPlateau n)
    (u.val i).val (F05Coord A i x,t)) = _
  calc
    _ = (∑ i,χ i x) * F05BCFFun (u.val j).val.1 (z,t) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => hTerm i)
    _ = _ := by rw [hSum x (hKV hx),one_mul]

end Yau.Proofs.F05Aux
