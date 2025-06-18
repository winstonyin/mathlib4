/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cocartesian monoidal category structure on commutative `R`-algebras

This file provides the cocartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

open CategoryTheory CartesianMonoidalCategory Limits TensorProduct

noncomputable section

namespace CommAlgCat
universe u v
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}

variable (A B) in
/-- The explicit cocone with tensor products as the fibered product in `CommAlgCat`. -/
def binaryCofan : BinaryCofan A B :=
  .mk (ofHom Algebra.TensorProduct.includeLeft)
    (ofHom (Algebra.TensorProduct.includeRight (A := A)))

variable (A B) in
@[simp]
lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom Algebra.TensorProduct.includeLeft := rfl

variable (A B) in
@[simp]
lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom Algebra.TensorProduct.includeRight := rfl

variable (A B) in
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

variable (A B) in
/-- Verify that the pushout cocone is indeed the colimit. -/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine Algebra.TensorProduct.liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/-- The initial object of `CommAlgCat R` is `R` as an algebra over itself -/
def isInitialSelf : IsInitial (of R R) := .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A))
  fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

open Opposite Algebra.TensorProduct CommAlgCat MonoidalCategory

attribute [local simp] Algebra.TensorProduct.one_def in
instance : MonoidalCategory (CommAlgCat.{u} R) where
  tensorObj S T := of R (S ⊗[R] T)
  whiskerLeft _ {_ _} f := ofHom (Algebra.TensorProduct.map (.id _ _) f.hom)
  whiskerRight {_ _} f T := ofHom (Algebra.TensorProduct.map f.hom (.id _ _))
  tensorHom {_ _ _ _} f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator {_ _ _} := isoMk (Algebra.TensorProduct.assoc R R _ _ _)
  leftUnitor _ := isoMk (Algebra.TensorProduct.lid R _)
  rightUnitor _ := isoMk (Algebra.TensorProduct.rid R R _)

@[simp] lemma coe_tensorUnit : 𝟙_ (CommAlgCat.{u} R) = R := rfl
@[simp] lemma coe_tensorObj (A B : CommAlgCat.{u} R) : A ⊗ B = A ⊗[R] B := rfl

@[simp] lemma tensorHom_hom {A B C D : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ D) :
    (f ⊗ₘ g).hom = Algebra.TensorProduct.map f.hom g.hom := rfl

@[simp] lemma rightWhisker_hom (f : A ⟶ B) (C : CommAlgCat.{u} R) :
    (f ▷ C).hom = Algebra.TensorProduct.map f.hom (.id _ _) := rfl

@[simp] lemma leftWhisker_hom (C : CommAlgCat.{u} R) (f : A ⟶ B) :
    (C ◁ f).hom = Algebra.TensorProduct.map (.id _ _) f.hom := rfl

@[simp] lemma associator_hom_hom (A B C : CommAlgCat.{u} R) :
    (α_ A B C).hom.hom = (Algebra.TensorProduct.assoc R R A B C).toAlgHom := rfl

@[simp] lemma associator_inv_hom (A B C : CommAlgCat.{u} R) :
    (α_ A B C).inv.hom = (Algebra.TensorProduct.assoc R R A B C).symm.toAlgHom := rfl

instance : BraidedCategory (CommAlgCat.{u} R) where
  braiding S T := isoMk (Algebra.TensorProduct.comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

@[simp] lemma braiding_hom_hom (A B : CommAlgCat.{u} R) :
    (β_ A B).hom.hom = (Algebra.TensorProduct.comm R A B).toAlgHom := rfl

@[simp] lemma braiding_inv_hom (A B : CommAlgCat.{u} R) :
    (β_ A B).inv.hom = (Algebra.TensorProduct.comm R B A).toAlgHom := rfl

attribute [local ext] Quiver.Hom.unop_inj in
instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T :=
    BinaryCofan.IsColimit.op <| binaryCofanIsColimit (unop S) (unop T)
  fst_def S T := by ext x; show x ⊗ₜ 1 = x ⊗ₜ algebraMap R (unop T:) 1; simp
  snd_def S T := by ext x; show 1 ⊗ₜ x = algebraMap R (unop S:) 1 ⊗ₜ x; simp

variable {A B C D : (CommAlgCat.{u} R)ᵒᵖ}

@[simp] lemma fst_unop_hom (A B : (CommAlgCat R)ᵒᵖ) :
    (fst A B).unop.hom = Algebra.TensorProduct.includeLeft := rfl

@[simp] lemma snd_unop_hom (A B : (CommAlgCat R)ᵒᵖ) :
    (snd A B).unop.hom = Algebra.TensorProduct.includeRight := rfl

@[simp] lemma toUnit_unop_hom (A : (CommAlgCat R)ᵒᵖ) :
    (toUnit A).unop.hom = Algebra.ofId R A.unop := rfl

@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = Algebra.TensorProduct.lift f.unop.hom g.unop.hom (fun _ _ ↦ .all _ _) :=
  rfl

end CommAlgCat
