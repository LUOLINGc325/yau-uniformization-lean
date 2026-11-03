import Yau.Proofs.D06Wold

/-! The shifted wandering basis is an actual Hilbert basis. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {r : ℕ}

def shiftedWanderingBasis (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ) : ℕ × Fin r → E :=
  fun ki => (S ^ ki.1) (b ki.2 : E)

omit [CompleteSpace E] in
theorem inner_pow_eq_of_le (S : E →ₗᵢ[ℂ] E) (k l : ℕ) (hkl : k ≤ l)
    (x y : E) : inner ℂ ((S ^ k) x) ((S ^ l) y) = inner ℂ x ((S ^ (l - k)) y) := by
  have hpow : S ^ l = S ^ k * S ^ (l - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkl]
  rw [hpow]
  change inner ℂ ((S ^ k) x) ((S ^ k) ((S ^ (l - k)) y)) = _
  exact (S ^ k).inner_map_map x ((S ^ (l - k)) y)

omit [CompleteSpace E] in
theorem wandering_inner_shift_eq_zero (S : E →ₗᵢ[ℂ] E) (x y : E)
    (hx : x ∈ S.rangeᗮ) (k : ℕ) (hk : 0 < k) : inner ℂ x ((S ^ k) y) = 0 := by
  have hy : (S ^ k) y ∈ S.range := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    refine ⟨(S ^ j) y, ?_⟩
    rw [pow_succ']
    rfl
  exact Submodule.inner_left_of_mem_orthogonal hy hx

omit [CompleteSpace E] in
theorem shiftedWanderingBasis_orthonormal (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ) :
    Orthonormal ℂ (shiftedWanderingBasis S b) := by
  rw [orthonormal_iff_ite]
  rintro ⟨k, i⟩ ⟨l, j⟩
  dsimp only [shiftedWanderingBasis]
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · rw [inner_pow_eq_of_le S k l hkl.le]
    rw [wandering_inner_shift_eq_zero S _ _ (b i).property _ (Nat.sub_pos_of_lt hkl)]
    simp [ne_of_lt hkl]
  · subst l
    rw [LinearIsometry.inner_map_map]
    have hb := (orthonormal_iff_ite.mp b.orthonormal) i j
    change inner ℂ (b i : E) (b j : E) = _ at hb
    simpa only [Prod.mk.injEq, true_and] using hb
  · have hzero : inner ℂ ((S ^ l) (b j : E)) ((S ^ k) (b i : E)) = 0 := by
      rw [inner_pow_eq_of_le S l k hkl.le]
      exact wandering_inner_shift_eq_zero S _ _ (b j).property _ (Nat.sub_pos_of_lt hkl)
    rw [inner_eq_zero_symm.mpr hzero]
    simp [ne_of_gt hkl]

omit [CompleteSpace E] in
theorem wanderingOrbit_le_span_shifted (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ) :
    wanderingOrbitSubmodule S ≤ Submodule.span ℂ (Set.range (shiftedWanderingBasis S b)) := by
  apply iSup_le
  intro k v hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hwrepr : (∑ i, b.repr ⟨w, hw⟩ i • (b i : E)) = w := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg (fun z : S.rangeᗮ => (z : E)) (b.sum_repr ⟨w, hw⟩)
  change (S ^ k) w ∈ _
  rw [← hwrepr, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(k, i), rfl⟩

def pureShiftHilbertBasis (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) : HilbertBasis (ℕ × Fin r) ℂ E :=
  HilbertBasis.mk (shiftedWanderingBasis_orthonormal S b) (by
    rw [← wanderingOrbit_dense_of_pure S hpure]
    exact Submodule.topologicalClosure_mono (wanderingOrbit_le_span_shifted S b))

end Yau.NodeProofs.D06Aux
