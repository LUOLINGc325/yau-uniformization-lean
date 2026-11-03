import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite-rank splitting along one section and its actual ambient dual.
The kernel, projected generators and adjoined frame remain in the same fiber. -/

open Set

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def kernelPart (B : Submodule ℂ E) (a : E →L[ℂ] ℂ) : Submodule ℂ E :=
  B ⊓ LinearMap.ker a.toLinearMap

def splitProjection (e : E) (a : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - a.smulRight e

theorem splitProjection_apply (e : E) (a : E →L[ℂ] ℂ) (v : E) :
    splitProjection e a v = v - a v • e := rfl

theorem splitProjection_mem {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    (he : e ∈ B) (hae : a e = 1) {v : E} (hv : v ∈ B) :
    splitProjection e a v ∈ kernelPart B a := by
  refine ⟨B.sub_mem hv (B.smul_mem _ he), ?_⟩
  change a (v - a v • e) = 0
  simp [hae]

theorem splitProjection_fix {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    {v : E} (hv : v ∈ kernelPart B a) : splitProjection e a v = v := by
  have hzero : a v = 0 := hv.2
  simp [splitProjection_apply, hzero]

theorem splitProjection_map {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    (he : e ∈ B) (hae : a e = 1) :
    B.map (splitProjection e a).toLinearMap = kernelPart B a := by
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact splitProjection_mem he hae hw
  · intro v hv
    exact ⟨v, hv.1, splitProjection_fix hv⟩

theorem split_generators_span {ι : Type*} {B : Submodule ℂ E}
    {e : E} {a : E →L[ℂ] ℂ} (he : e ∈ B) (hae : a e = 1)
    {s : ι → E} (hs : Submodule.span ℂ (Set.range s) = B) :
    Submodule.span ℂ (Set.range fun i => splitProjection e a (s i)) = kernelPart B a := by
  have hr : Set.range (fun i => splitProjection e a (s i)) =
      (splitProjection e a) '' Set.range s := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s i, Set.mem_range_self i, rfl⟩
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
  rw [hr]
  calc
    Submodule.span ℂ ((splitProjection e a) '' Set.range s) =
        (Submodule.span ℂ (Set.range s)).map (splitProjection e a).toLinearMap :=
      (Submodule.map_span (splitProjection e a).toLinearMap _).symm
    _ = kernelPart B a := by rw [hs, splitProjection_map he hae]

theorem split_span_sup {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    (he : e ∈ B) (hae : a e = 1) :
    Submodule.span ℂ {e} ⊔ kernelPart B a = B := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem e B).mpr he) inf_le_left
  · intro v hv
    apply Submodule.mem_sup.mpr
    refine ⟨a v • e, Submodule.mem_span_singleton.mpr ⟨a v, rfl⟩,
      splitProjection e a v, splitProjection_mem he hae hv, ?_⟩
    simp [splitProjection_apply]

theorem split_span_disjoint {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    (hae : a e = 1) : Disjoint (Submodule.span ℂ {e}) (kernelPart B a) := by
  apply Submodule.disjoint_def.mpr
  intro v hv heker
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hc : c = 0 := by
    have hz : a (c • e) = 0 := heker.2
    simpa [hae] using hz
  simp [hc]

theorem split_kernel_finrank [FiniteDimensional ℂ E] {B : Submodule ℂ E}
    {e : E} {a : E →L[ℂ] ℂ} (he : e ∈ B) (hae : a e = 1)
    {r : ℕ} (hr : Module.finrank ℂ B = r + 1) :
    Module.finrank ℂ (kernelPart B a) = r := by
  have hene : e ≠ 0 := by
    intro hzero
    simpa [hzero] using hae
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℂ {e}) (kernelPart B a)
  rw [split_span_sup he hae, (split_span_disjoint hae).eq_bot,
    finrank_bot, add_zero, finrank_span_singleton hene, hr] at hd
  omega

theorem adjoin_kernel_frame {B : Submodule ℂ E} {e : E} {a : E →L[ℂ] ℂ}
    (he : e ∈ B) (hae : a e = 1) {r : ℕ} {v : Fin r → E}
    (hv : LinearIndependent ℂ v)
    (hspan : Submodule.span ℂ (Set.range v) = kernelPart B a) :
    LinearIndependent ℂ (Fin.cons e v) ∧
      Submodule.span ℂ (Set.range (Fin.cons e v)) = B := by
  have hene : e ∉ Submodule.span ℂ (Set.range v) := by
    intro hm
    rw [hspan] at hm
    have hz : a e = 0 := hm.2
    exact one_ne_zero (hae.symm.trans hz)
  refine ⟨hv.finCons hene, ?_⟩
  rw [Fin.range_cons, Submodule.span_insert, hspan, split_span_sup he hae]

end Yau.Blueprint.D05Proof
