import Yau.Blueprint.DiscFrames

/-! V01 scratch source: the cotangent immersion uses the one finite base
immersion and the one finite global spanning tuple supplied by original P03. -/

noncomputable section

namespace Yau.Blueprint.V01Proof

theorem linearMap_eq_of_spanning
    {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ}
    (V : Fin m → E) (hspan : Submodule.span ℂ (Set.range V) = ⊤)
    {ξ η : E →ₗ[ℂ] ℂ} (hagree : ∀ i, ξ (V i) = η (V i)) : ξ = η := by
  apply LinearMap.ext
  intro v
  let L : E →ₗ[ℂ] ℂ := ξ - η
  have hle : Submodule.span ℂ (Set.range V) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ξ (V i) - η (V i) = 0
    exact sub_eq_zero.mpr (hagree i)
  have hker : v ∈ LinearMap.ker L := hle (by rw [hspan]; trivial)
  change ξ v - η v = 0 at hker
  exact sub_eq_zero.mp hker

variable {n N m : ℕ} {M : ComplexManifold n}

theorem covector_eq_of_spanning (x : M.Carrier)
    (V : Fin m → TangentVector M x)
    (hspan : Submodule.span ℂ (Set.range V) = ⊤)
    {ξ η : Covector n} (hagree : ∀ j, ξ (V j) = η (V j)) : ξ = η := by
  let ξL : TangentVector M x →ₗ[ℂ] ℂ :=
    { toFun := fun v => ξ v
      map_add' := fun v w => ξ.map_add v w
      map_smul' := fun c v => ξ.map_smul c v }
  let ηL : TangentVector M x →ₗ[ℂ] ℂ :=
    { toFun := fun v => η v
      map_add' := fun v w => η.map_add v w
      map_smul' := fun c v => η.map_smul c v }
  have hL : ξL = ηL := linearMap_eq_of_spanning V hspan hagree
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun hL v

def cotangentEmbedding (F : M.Carrier → ComplexVector N)
    (V : Fin m → VectorField M) (y : CotangentPoint M) : ComplexVector (N + m) :=
  WithLp.toLp 2 (Fin.addCases (fun i => F y.1 i) (fun j => y.2 (V j y.1)))

theorem cotangentEmbedding_base (F : M.Carrier → ComplexVector N)
    (V : Fin m → VectorField M) (y : CotangentPoint M) (i : Fin N) :
    cotangentEmbedding F V y (Fin.castAdd m i) = F y.1 i := by
  simp [cotangentEmbedding]

theorem cotangentEmbedding_fiber (F : M.Carrier → ComplexVector N)
    (V : Fin m → VectorField M) (y : CotangentPoint M) (j : Fin m) :
    cotangentEmbedding F V y (Fin.natAdd N j) = y.2 (V j y.1) := by
  simp [cotangentEmbedding]

theorem cotangentEmbedding_injective
    (F : M.Carrier → ComplexVector N) (hF : Function.Injective F)
    (V : Fin m → VectorField M)
    (hspan : ∀ x, Submodule.span ℂ (Set.range (fun i => V i x)) = ⊤) :
    Function.Injective (cotangentEmbedding F V) := by
  rintro ⟨x, ξ⟩ ⟨y, η⟩ heq
  have hbase : F x = F y := by
    ext i
    have hi := congrArg (fun w : ComplexVector (N + m) => w (Fin.castAdd m i)) heq
    simpa only [cotangentEmbedding_base] using hi
  have hxy : x = y := hF hbase
  subst y
  have hξη : ξ = η := covector_eq_of_spanning x (fun i => V i x) (hspan x) (by
    intro j
    have hj := congrArg (fun w : ComplexVector (N + m) => w (Fin.natAdd N j)) heq
    simpa only [cotangentEmbedding_fiber] using hj)
  exact congrArg (fun ζ : Covector n => (x, ζ)) hξη

end Yau.Blueprint.V01Proof
