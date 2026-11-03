import Yau.Geometry.Basic

/-!
Only the concrete global-coordinate endpoint remains here.  The previous
inverse-tube, convergence, and surjectivity records were proposition-valued
shells and are deleted until their estimates are proved.
-/

namespace Yau.Uniformization

open Yau

/-! Pre-surjectivity data.  The image is a range, and no diffeomorphism onto
`ℂⁿ` is stored here; the latter is constructed only after the U03 radius
contradiction. -/
structure OpenCoordinateData (n : ℕ) (M : ComplexManifold n) where
  dimension_pos : 1 ≤ n
  map : M.Carrier → (ComplexEuclideanManifold n dimension_pos).Carrier
  injective : Function.Injective map
  inverse : {z // z ∈ (Set.range map)} → M.Carrier
  left_inverse : ∀ x, inverse ⟨map x, by exact ⟨x, rfl⟩⟩ = x
  right_inverse : ∀ z : {z // z ∈ (Set.range map)}, map (inverse z) = z.1
  image_open : IsOpen (Set.range map)
  map_holomorphic : IsHolomorphicMap (M := M)
    (N := ComplexEuclideanManifold n dimension_pos) map
  inverse_extension : (ComplexEuclideanManifold n dimension_pos).Carrier → M.Carrier
  inverse_contMDiffOn : ContMDiffOn (ComplexModel n) (ComplexModel n) ⊤
    inverse_extension (Set.range map)
  inverse_complex_linear_on : ∀ (z : (ComplexEuclideanManifold n dimension_pos).Carrier),
    z ∈ (Set.range map) → ∀ (a : ℂ) (v : TangentSpace (ComplexModel n) z),
      mfderiv (ComplexModel n) (ComplexModel n) inverse_extension z (a • v) =
        a • mfderiv (ComplexModel n) (ComplexModel n) inverse_extension z v
  inverse_extension_on_image : ∀ z : {z // z ∈ (Set.range map)}, inverse_extension z.1 = inverse z

/-- The coordinate image is computed from the actual map, never caller-supplied. -/
def OpenCoordinateData.image {n : ℕ} {M : ComplexManifold n}
    (D : OpenCoordinateData n M) := Set.range D.map

theorem OpenCoordinateData.image_def {n : ℕ} {M : ComplexManifold n}
    (D : OpenCoordinateData n M) : D.image = Set.range D.map := rfl

structure GlobalCoordinateData (n : ℕ) where
  manifold : ComplexManifold n
  dimension_pos : 1 ≤ n
  diffeomorph :
    Diffeomorph (ComplexModel n) (ComplexModel n) manifold.Carrier
      (ComplexEuclideanManifold n dimension_pos).Carrier ⊤
  mapHolomorphic : IsHolomorphicMap (M := manifold)
    (N := ComplexEuclideanManifold n dimension_pos) (fun x => diffeomorph x)
  inverseHolomorphic : IsHolomorphicMap (M := ComplexEuclideanManifold n dimension_pos)
    (N := manifold) (fun z => diffeomorph.symm z)

/- Once the open coordinate image is proved to be all of `ℂⁿ`, the inverse
   extension already stored in `OpenCoordinateData` supplies the global
   diffeomorphism.  This is the concrete U03→U04 bridge; no biholomorphism is
   accepted as an extra caller-filled premise. -/
noncomputable def OpenCoordinateData.toGlobal
    {n : ℕ} {M : ComplexManifold n} (D : OpenCoordinateData n M)
    (hsurj : D.image = Set.univ) : GlobalCoordinateData n := by
  let e : M.Carrier ≃ (ComplexEuclideanManifold n D.dimension_pos).Carrier :=
    { toFun := D.map
      invFun := D.inverse_extension
      left_inv := by
        intro x
        calc
          D.inverse_extension (D.map x) =
              D.inverse ⟨D.map x, by exact ⟨x, rfl⟩⟩ := by
                simpa using D.inverse_extension_on_image
                  ⟨D.map x, by exact ⟨x, rfl⟩⟩
          _ = x := D.left_inverse x
      right_inv := by
        intro z
        have hz : z ∈ D.image := by rw [hsurj]; trivial
        calc
          D.map (D.inverse_extension z) = D.map (D.inverse ⟨z, hz⟩) := by
            congr 1
            simpa using D.inverse_extension_on_image ⟨z, hz⟩
          _ = z := D.right_inverse ⟨z, hz⟩ }
  have hrange : Set.range D.map = Set.univ := hsurj
  have hinv : ContMDiff (ComplexModel n) (ComplexModel n) ⊤ D.inverse_extension :=
    contMDiffOn_univ.mp (by simpa [hrange] using D.inverse_contMDiffOn)
  let ed : Diffeomorph (ComplexModel n) (ComplexModel n) M.Carrier
      (ComplexEuclideanManifold n D.dimension_pos).Carrier ⊤ :=
    ⟨e, D.map_holomorphic.1, by simpa [e] using hinv⟩
  have hinvhol : IsHolomorphicMap (M := ComplexEuclideanManifold n D.dimension_pos)
      (N := M) (fun z => ed.symm z) := by
    refine ⟨?_, ?_⟩
    · change ContMDiff (ComplexModel n) (ComplexModel n) ⊤ D.inverse_extension
      exact hinv
    · intro z a v
      simpa [ed, e] using D.inverse_complex_linear_on z (by simpa [hrange]) a v
  exact ⟨M, D.dimension_pos, ed, D.map_holomorphic, hinvhol⟩

theorem GlobalCoordinateData.biholomorphic
    (D : GlobalCoordinateData n) :
    BiholomorphicToComplexEuclidean D.manifold := by
  exact ⟨⟨D.dimension_pos, D.diffeomorph, D.mapHolomorphic, D.inverseHolomorphic⟩⟩

end Yau.Uniformization
